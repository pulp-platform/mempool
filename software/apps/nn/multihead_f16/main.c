// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp_postmod.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_redmule_f16.h"
#include "baremetal/mempool_softmax_f16.h"

#include "data_multihead_f16.h"

#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))
#define SHIFT (false)
#define VERBOSE (false)
#ifndef VERIFY_TOL
#define VERIFY_TOL (0.01f)
#endif

__fp16 l1_X[H * M * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Wq[N * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Wk[N * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Wv[N * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_QKV[3 * H * M * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Kt[H * M * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_A[H * M * M]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_S[H * M * M]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

void inline transpose_K(__fp16 *K, __fp16 *Kt, uint32_t size_H, uint32_t size_M,
                        uint32_t size_N, uint32_t core_id, uint32_t num_cores) {
  for (uint32_t idx = core_id * 16; idx < size_H * size_M * size_N;
       idx += num_cores * 16) {
    uint32_t i_h = idx / (size_M * size_N);
    uint32_t i_m = (idx % (size_M * size_N)) / size_N;
    uint32_t i_n = (idx % (size_M * size_N)) % size_N;
    uint32_t dst = i_h * size_N * size_M + i_n * size_M + i_m;
    __fp16 *addr_src = K + idx;
    __fp16 *addr_dst = Kt + dst;
    const uint32_t k_incr = size_M * 2;
    __fp16 K00, K01, K02, K03, K04, K05, K06, K07;
    __fp16 K08, K09, K10, K11, K12, K13, K14, K15;
    asm volatile("lh %[K00], 0(%[addr_src]) \n\t"
                 "lh %[K01], 2(%[addr_src]) \n\t"
                 "lh %[K02], 4(%[addr_src]) \n\t"
                 "lh %[K03], 6(%[addr_src]) \n\t"
                 "lh %[K04], 8(%[addr_src]) \n\t"
                 "lh %[K05], 10(%[addr_src]) \n\t"
                 "lh %[K06], 12(%[addr_src]) \n\t"
                 "lh %[K07], 14(%[addr_src]) \n\t"
                 "lh %[K08], 16(%[addr_src]) \n\t"
                 "lh %[K09], 18(%[addr_src]) \n\t"
                 "lh %[K10], 20(%[addr_src]) \n\t"
                 "lh %[K11], 22(%[addr_src]) \n\t"
                 "lh %[K12], 24(%[addr_src]) \n\t"
                 "lh %[K13], 26(%[addr_src]) \n\t"
                 "lh %[K14], 28(%[addr_src]) \n\t"
                 "lh %[K15], 30(%[addr_src]) \n\t"
                 "p.sh.rrpost %[K00], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K01], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K02], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K03], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K04], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K05], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K06], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K07], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K08], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K09], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K10], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K11], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K12], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K13], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K14], (%[addr_dst]), %[k_incr] \n\t"
                 "p.sh.rrpost %[K15], (%[addr_dst]), %[k_incr] \n\t"
                 : [K00] "+&r"(K00), [K01] "+&r"(K01), [K02] "+&r"(K02),
                   [K03] "+&r"(K03), [K04] "+&r"(K04), [K05] "+&r"(K05),
                   [K06] "+&r"(K06), [K07] "+&r"(K07), [K08] "+&r"(K08),
                   [K09] "+&r"(K09), [K10] "+&r"(K10), [K11] "+&r"(K11),
                   [K12] "+&r"(K12), [K13] "+&r"(K13), [K14] "+&r"(K14),
                   [K15] "+&r"(K15), [addr_dst] "+r"(addr_dst)
                 : [addr_src] "r"(addr_src), [k_incr] "r"(k_incr)
                 : "memory");
  }
  return;
}

void checkpoint_printf(const char *fmt, bool verbose) {
  if (verbose) {
    if (mempool_get_core_id() == 0) {
      printf("/*********************************************************/\n");
      printf("/* DONE: %s\n", fmt);
      printf("/*********************************************************/\n\n");
    }
    mempool_barrier(NUM_CORES);
  }
}

int main() {

  /* Initialization */
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  /* Allocate */
  static __fp16 *Q = l1_QKV;
  static __fp16 *K = &l1_QKV[H * M * N];
  static __fp16 *V = &l1_QKV[2 * H * M * N];

  /* L1 transfer */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, (H * M * N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Wq, l2_Wq, N * N * sizeof(int16_t));
    dma_memcpy_blocking(l1_Wk, l2_Wk, N * N * sizeof(int16_t));
    dma_memcpy_blocking(l1_Wv, l2_Wv, N * N * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

#ifdef DOUBLE_BUFFERING

  /* Generate K */
  mempool_start_benchmark();
  redmule_synch_parallel(l1_X, l1_Wk, K, H * M, N, N, MATMUL, SHIFT,
                         PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Generate K", VERBOSE);

  /* Compute Q */
  mempool_start_benchmark();
  redmule_asynch_parallel(l1_X, l1_Wq, Q, H * M, N, N, MATMUL, SHIFT,
                          PORT_WIDTH);
  mempool_stop_benchmark();

  /* Transpose */
  mempool_start_benchmark();
  transpose_K(K, l1_Kt, H, M, N, core_id, num_cores);
  mempool_stop_benchmark();

  /* Wait for RedMulE */
  mempool_start_benchmark();
  wait_redmule();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  /* Compute V */
  mempool_start_benchmark();
  redmule_synch_parallel(l1_X, l1_Wv, V, H * M, N, N, MATMUL, SHIFT,
                         PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Linear (I -> QKV) & Transposition", VERBOSE);

#else

  /* QKV generation */
  mempool_start_benchmark();

  redmule_asynch_parallel(l1_X, l1_Wq, Q, H * M, N, N, MATMUL, SHIFT,
                          PORT_WIDTH);
  wait_redmule();

  redmule_asynch_parallel(l1_X, l1_Wk, K, H * M, N, N, MATMUL, SHIFT,
                          PORT_WIDTH);
  wait_redmule();

  redmule_asynch_parallel(l1_X, l1_Wv, V, H * M, N, N, MATMUL, SHIFT,
                          PORT_WIDTH);
  wait_redmule();

  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Linear (I -> QKV)", VERBOSE);

  mempool_start_benchmark();
  transpose_K(K, l1_Kt, H, M, N, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Transpose", VERBOSE);

#endif

  /* Allocate A */
  static __fp16 *A = l1_A;
  static __fp16 *S = l1_S;

  // /* A = Q * Kt */
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  if (redmule_id < num_redmules) {
    mempool_start_benchmark();
    for (uint32_t ih = redmule_id; ih < H; ih += num_redmules) {
      redmule_asynch_single(&Q[ih * (M * N)], &l1_Kt[ih * (N * M)],
                            &A[ih * (M * M)], M, N, M, MATMUL, redmule_id);
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  /* Softmax */
  mempool_start_benchmark();
  softmax_parallel_2x4_f16vec(A, S, H * M, M, core_id, num_cores);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  /* Softmax(A) * V */
  if (redmule_id < num_redmules) {
    mempool_start_benchmark();
    for (uint32_t ih = redmule_id; ih < H; ih += num_redmules) {
      redmule_asynch_single(&S[ih * (M * M)], &V[ih * (M * N)],
                            &l1_X[ih * (M * N)], M, M, N, MATMUL, redmule_id);
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Head-wise Attention", VERBOSE);

  /* L1 transfer */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l2_Y, l1_X, (H * M * N) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Transfer-out", VERBOSE);

#ifdef VERIFY
  /* Compare the output (copied back to l2_Y) with the numpy reference l2_Z */
  mempool_check_f16(l2_Y, l2_Z, H * M * N, VERIFY_TOL, 0);
  mempool_barrier(num_cores);
#endif

  return 0;
}
