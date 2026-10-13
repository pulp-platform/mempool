// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "hal_redmule.h"

#include "baremetal/mempool_softmax_f16.h"
#include "builtins_v2.h"

// Smallest slice of rows of a batch given to one RedMulE
#ifndef ATTENTION_MIN_SLICE_ROWS
#define ATTENTION_MIN_SLICE_ROWS (32)
#endif

/* Start one RedMulE GEMM: O (M x P) = I (M x N) * W (N x P) */
static inline void attention_gemm_start(__fp16 const *I, __fp16 const *W,
                                        __fp16 *O, uint32_t M, uint32_t N,
                                        uint32_t P) {
  hwpe_soft_clear();
  mempool_wait(10);
  redmule_cfg((unsigned int)I, (unsigned int)W, (unsigned int)O, (uint16_t)M,
              (uint16_t)N, (uint16_t)P, 0, MATMUL, Float16);
  mempool_wait(10);
  hwpe_trigger_job();
}

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
                 the Q * Kt of the next round.
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
                         __fp16 const *__restrict__ V,
                         __fp16 *__restrict__ Aw, __fp16 *__restrict__ A,
                         uint32_t Batch, uint32_t SeqLen, uint32_t tdEmbed,
                         uint32_t slot_q, uint32_t slot_s, uint32_t core_id,
                         uint32_t num_cores) {

  // The scores and the attention output share A
  __fp16 *scores = A;

  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  // Slices per batch: one job per RedMulE, of at least MIN_SLICE_ROWS rows
  uint32_t slices = num_redmules / Batch;
  uint32_t max_slices = SeqLen / ATTENTION_MIN_SLICE_ROWS;
  slices = (slices > max_slices) ? max_slices : slices;
  slices = (slices == 0) ? 1 : slices;
  uint32_t rows = SeqLen / slices;
  uint32_t jobs = Batch * slices;

#ifdef PIPELINED
  // Pipelined Q*Kt and Softmax
  // Round r: RedMulEs compute Q*Kt for jobs [r*R, (r+1)*R), while all
  // cores compute the softmax of the jobs produced in round r-1.
  // One extra round drains the softmax of the last jobs.
  mempool_start_benchmark();
  for (uint32_t jb = 0; jb < jobs + num_redmules; jb += num_redmules) {

    // Launch Q*Kt of the current jobs
    uint32_t j = jb + redmule_id;
    uint32_t launched = (redmule_id < num_redmules) && (j < jobs);
    if (launched) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      attention_gemm_start(Q + b * slot_q + r0 * tdEmbed, Kt + b * slot_q,
                           scores + b * slot_s + r0 * SeqLen, rows, tdEmbed,
                           SeqLen);
    }

    // Softmax of the jobs computed in the previous round
    if (jb > 0) {
      uint32_t prev = jb - num_redmules;
      uint32_t n = (jobs - prev < num_redmules) ? (jobs - prev) : num_redmules;
      attention_softmax(scores, Aw, prev, n, slices, rows, SeqLen, slot_s,
                        core_id, num_cores);
    }

    // Wait for RedMulE (the wake-up is latched if the job already finished)
    if (launched) {
      mempool_wfi();
    }
    mempool_barrier(num_cores);
  }
  mempool_stop_benchmark();
#else
  // Q*Kt
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t j = redmule_id; j < jobs; j += num_redmules) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      attention_gemm_start(Q + b * slot_q + r0 * tdEmbed, Kt + b * slot_q,
                           scores + b * slot_s + r0 * SeqLen, rows, tdEmbed,
                           SeqLen);
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // Softmax
  mempool_start_benchmark();
  attention_softmax(scores, Aw, 0, jobs, slices, rows, SeqLen, slot_s,
                    core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  // A = Softmax(Q*Kt)*V
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t j = redmule_id; j < jobs; j += num_redmules) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      attention_gemm_start(Aw + b * slot_s + r0 * SeqLen, V + b * slot_q,
                           A + b * slot_q + r0 * tdEmbed, rows, SeqLen,
                           tdEmbed);
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  return;
}
