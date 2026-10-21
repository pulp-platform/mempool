// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "hal_redmule.h"

#include "baremetal/mempool_redmule_f16.h"
#include "baremetal/mempool_softmax_f16.h"
#include "builtins_v2.h"

// Smallest slice of rows of a batch given to one RedMulE
#ifndef ATTENTION_MIN_SLICE_ROWS
#define ATTENTION_MIN_SLICE_ROWS (32)
#endif

// Rounds of jobs per RedMulE. With more than one, each batch is split into
// more slices and, with PIPELINED, the softmax of a round overlaps with the
// Q * Kt of the next round and with the A * V of the previous one; Q * Kt,
// softmax and A * V are then one benchmark region.
#ifndef ATTENTION_ROUNDS
#define ATTENTION_ROUNDS (1)
#endif

/* Softmax of the jobs [first, first + n), num_cores / n cores per job */
static inline void attention_softmax(__fp16 const *scores, __fp16 *Aw,
                                     uint32_t first, uint32_t n,
                                     uint32_t slices, uint32_t rows,
                                     uint32_t SeqLen, uint32_t slot_s,
                                     uint32_t core_id, uint32_t num_cores) {
  if (n < num_cores) {
    uint32_t num_cores_per_softmax = num_cores / n;
    uint32_t softmax_id = core_id % num_cores_per_softmax;
    uint32_t idx = core_id / num_cores_per_softmax;
    if (idx < n) {
      uint32_t j = first + idx;
      uint32_t off = (j / slices) * slot_s + (j % slices) * rows * SeqLen;
      softmax_parallel_2x4_f16vec(&scores[off], &Aw[off], rows, SeqLen,
                                  softmax_id, num_cores_per_softmax);
    }
  } else {
    for (uint32_t j = first + core_id; j < first + n; j += num_cores) {
      uint32_t off = (j / slices) * slot_s + (j % slices) * rows * SeqLen;
      softmax_parallel_2x4_f16vec(&scores[off], &Aw[off], rows, SeqLen, 0, 1);
    }
  }
}

/**
  @brief         Computes scaled dot-product attention.
  @details       Performs the operation:
                   A = Softmax(Q * Kt) * V
                 independently for each batch, on the RedMulEs.
                 The RedMulE jobs are slices of rows of a batch: with fewer
                 batches than RedMulEs, each batch is split into up to
                 SeqLen / ATTENTION_MIN_SLICE_ROWS slices so that every
                 RedMulE gets a job. Rows of Q * Kt, of the softmax and of A
                 depend only on the same rows of Q, of the scores and of Aw.
                 Assumes power-of-two RedMulEs, Batch and SeqLen.
                 With PIPELINED, the softmax of a round of jobs overlaps with
                 the Q * Kt of the next round. ATTENTION_ROUNDS > 1 gives each
                 RedMulE that many rounds (up to the minimum slice size) and
                 also overlaps the Aw * V of a round with the next softmax.
  @param[in]     Q         Query tensor, [Batch][SeqLen][tdEmbed]
  @param[in]     Kt        Key tensor (transposed), [Batch][tdEmbed][SeqLen]
  @param[in]     V         Value tensor, [Batch][SeqLen][tdEmbed]
  @param[out]    Aw        Softmax output, [Batch][SeqLen][SeqLen]
  @param[out]    A         Attention scores Q * Kt, [Batch][SeqLen][SeqLen],
                           then attention output, [Batch][SeqLen][tdEmbed]
  @param[in]     Batch     Number of batches
  @param[in]     SeqLen    Sequence Length
  @param[in]     tdEmbed   Temporal embedding dimension
  @param[in]     slot_q    Elements between the batches of Q, Kt, V and A
  @param[in]     slot_s    Elements between the batches of the scores and Aw
  @param[in]     core_id   Core ID
  @param[in]     num_cores Number of cores
  @return        none
*/

void attention_block_f16(__fp16 const *__restrict__ Q,
                         __fp16 const *__restrict__ Kt,
                         __fp16 const *__restrict__ V, __fp16 *__restrict__ Aw,
                         __fp16 *__restrict__ A, uint32_t Batch,
                         uint32_t SeqLen, uint32_t tdEmbed, uint32_t slot_q,
                         uint32_t slot_s, uint32_t core_id,
                         uint32_t num_cores) {

  // The scores and the attention output share A
  __fp16 *scores = A;

  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  // Slices per batch: one job per RedMulE, of at least MIN_SLICE_ROWS rows
  uint32_t slices = (ATTENTION_ROUNDS * num_redmules) / Batch;
  uint32_t max_slices = SeqLen / ATTENTION_MIN_SLICE_ROWS;
  slices = (slices > max_slices) ? max_slices : slices;
  slices = (slices == 0) ? 1 : slices;
  uint32_t rows = SeqLen / slices;
  uint32_t jobs = Batch * slices;

#ifdef PIPELINED
  // Pipelined Q*Kt, Softmax, and Aw*V
  // Round r: RedMulEs compute Q*Kt for jobs [r*R, (r+1)*R), while all
  // cores compute the softmax of the jobs produced in round r-1.
  // One extra round drains the softmax of the last jobs.
  mempool_start_benchmark();

#if ATTENTION_ROUNDS > 1
  // Two extra rounds drain the softmax and the Aw*V of the last jobs
  uint32_t rounds_end = jobs + 2 * num_redmules;
#else
  uint32_t rounds_end = jobs + num_redmules;
#endif

  for (uint32_t jb = 0; jb < rounds_end; jb += num_redmules) {

    // Launch Q*Kt of the current jobs
    uint32_t j = jb + redmule_id;
    uint32_t launched_qk = (redmule_id < num_redmules) && (j < jobs);
    if (launched_qk) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      redmule_start(Q + b * slot_q + r0 * tdEmbed, Kt + b * slot_q,
                    scores + b * slot_s + r0 * SeqLen, rows, tdEmbed, SeqLen, 0,
                    MATMUL);
    }

#if ATTENTION_ROUNDS > 1
    // Aw*V of the jobs whose softmax completed in the previous round. If the
    // RedMulE also has a Q*Kt in this round, the Aw*V is launched once the
    // Q*Kt completed.
    uint32_t jv = j - 2 * num_redmules;
    uint32_t launched_av = (redmule_id < num_redmules) &&
                           (jb >= 2 * num_redmules) && (jv < jobs);
    if (launched_av && !launched_qk) {
      uint32_t b = jv / slices, r0 = (jv % slices) * rows;
      redmule_start(Aw + b * slot_s + r0 * SeqLen, V + b * slot_q,
                    A + b * slot_q + r0 * tdEmbed, rows, SeqLen, tdEmbed, 0,
                    MATMUL);
    }
#endif

    // Softmax of the jobs computed in the previous round
    if (jb > 0 && jb - num_redmules < jobs) {
      uint32_t prev = jb - num_redmules;
      uint32_t n = (jobs - prev < num_redmules) ? (jobs - prev) : num_redmules;
      attention_softmax(scores, Aw, prev, n, slices, rows, SeqLen, slot_s,
                        core_id, num_cores);
    }

    // Wait for RedMulE executing the current Q*Kt iteration (the wake-up is
    // latched if the job already finished)
    if (launched_qk) {
      mempool_wfi();
    }

#if ATTENTION_ROUNDS > 1
    // If a Q*Kt iteration is ongoing the Aw*V launch is postponed
    if (launched_av && launched_qk) {
      uint32_t b = jv / slices, r0 = (jv % slices) * rows;
      redmule_start(Aw + b * slot_s + r0 * SeqLen, V + b * slot_q,
                    A + b * slot_q + r0 * tdEmbed, rows, SeqLen, tdEmbed, 0,
                    MATMUL);
    }

    // Wait for RedMulE executing the current Aw*V iteration (the wake-up is
    // latched if the job already finished)
    if (launched_av) {
      mempool_wfi();
    }
#endif

    mempool_barrier(num_cores);
  }

#if ATTENTION_ROUNDS > 1
  mempool_stop_benchmark();
#else
  mempool_stop_benchmark();
  // Complete the attention computation with Aw*V
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t j = redmule_id; j < jobs; j += num_redmules) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      redmule_start(Aw + b * slot_s + r0 * SeqLen, V + b * slot_q,
                    A + b * slot_q + r0 * tdEmbed, rows, SeqLen, tdEmbed, 0,
                    MATMUL);
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

#else
  // Fully serial implementation with no overlap of the PE and TE execution

  // Q*Kt
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t j = redmule_id; j < jobs; j += num_redmules) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      redmule_start(Q + b * slot_q + r0 * tdEmbed, Kt + b * slot_q,
                    scores + b * slot_s + r0 * SeqLen, rows, tdEmbed, SeqLen, 0,
                    MATMUL);
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // Softmax
  mempool_start_benchmark();
  attention_softmax(scores, Aw, 0, jobs, slices, rows, SeqLen, slot_s, core_id,
                    num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // A = Softmax(Q*Kt)*V
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t j = redmule_id; j < jobs; j += num_redmules) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      redmule_start(Aw + b * slot_s + r0 * SeqLen, V + b * slot_q,
                    A + b * slot_q + r0 * tdEmbed, rows, SeqLen, tdEmbed, 0,
                    MATMUL);
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#endif

  return;
}
