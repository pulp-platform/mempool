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

#include "baremetal/mempool_redmule_f16.h"
#include "baremetal/mempool_softmax_f16.h"

#include "data_multihead_f16.h"

#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))
#define SHIFT (false)
#define VERBOSE (false)

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
__fp16 l1_A[H * M * M]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_S[H * M * M]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 zeros[H * M * M]
    __attribute__((aligned(sizeof(int32_t)), section(".l2"))) = {0};

void inline transpose_K(__fp16 *K, uint32_t size_H, uint32_t size_M,
                        uint32_t size_N, uint32_t core_id, uint32_t num_cores) {
  for (uint32_t idx = core_id * 16; idx < size_H * size_M * size_N;
       idx += num_cores * 16) {
    uint32_t i_h = idx / (size_M * size_N);
    uint32_t i_m = (idx % (size_M * size_N)) / size_N;
    uint32_t i_n = (idx % (size_M * size_N)) % size_N;
    uint32_t dst = i_h * size_N * size_M + i_n * size_M + i_m;
    __fp16 *addr_src = K + idx;
    __fp16 *addr_dst = K + dst;
    const uint32_t k_incr = size_M * 2;
    __fp16 K00, K01, K02, K03, K04, K05, K06, K07;
    __fp16 K08, K09, K10, K11, K12, K13, K14, K15;
    asm volatile("lh %0,  0(%[addr_src]);"
                 "lh %1,  2(%[addr_src]);"
                 "lh %2,  4(%[addr_src]);"
                 "lh %3,  6(%[addr_src]);"
                 "lh %4,  8(%[addr_src]);"
                 "lh %5,  10(%[addr_src]);"
                 "lh %6,  12(%[addr_src]);"
                 "lh %7,  14(%[addr_src]);"
                 "lh %8,  16(%[addr_src]);"
                 "lh %9,  18(%[addr_src]);"
                 "lh %10, 20(%[addr_src]);"
                 "lh %11, 22(%[addr_src]);"
                 "lh %12, 24(%[addr_src]);"
                 "lh %13, 26(%[addr_src]);"
                 "lh %14, 28(%[addr_src]);"
                 "lh %15, 30(%[addr_src]);"
                 "p.sh %0, %[k_incr](%[addr_dst]);"
                 "p.sh %1, %[k_incr](%[addr_dst]);"
                 "p.sh %2, %[k_incr](%[addr_dst]);"
                 "p.sh %3, %[k_incr](%[addr_dst]);"
                 "p.sh %4, %[k_incr](%[addr_dst]);"
                 "p.sh %5, %[k_incr](%[addr_dst]);"
                 "p.sh %6, %[k_incr](%[addr_dst]);"
                 "p.sh %7, %[k_incr](%[addr_dst]);"
                 "p.sh %8, %[k_incr](%[addr_dst]);"
                 "p.sh %9, %[k_incr](%[addr_dst]);"
                 "p.sh %10, %[k_incr](%[addr_dst]);"
                 "p.sh %11, %[k_incr](%[addr_dst]);"
                 "p.sh %12, %[k_incr](%[addr_dst]);"
                 "p.sh %13, %[k_incr](%[addr_dst]);"
                 "p.sh %14, %[k_incr](%[addr_dst]);"
                 "p.sh %15, %[k_incr](%[addr_dst]);"
                 : "+&r"(K00), "+&r"(K01), "+&r"(K02), "+&r"(K03), "+&r"(K04),
                   "+&r"(K05), "+&r"(K06), "+&r"(K07), "+&r"(K08), "+&r"(K09),
                   "+&r"(K10), "+&r"(K11), "+&r"(K12), "+&r"(K13), "+&r"(K14),
                   "+&r"(K15), [addr_dst] "+&r"(addr_dst)
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
    dma_memcpy_blocking(Q, l2_Y, (H * M * N) * sizeof(int16_t));
    dma_memcpy_blocking(K, l2_Y, (H * M * N) * sizeof(int16_t));
    dma_memcpy_blocking(V, l2_Y, (H * M * N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_A, zeros, (H * M * M) * sizeof(int16_t));
    dma_memcpy_blocking(l1_S, zeros, (H * M * M) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

#ifdef DOUBLE_BUFFERING

  /* Generate K */
  mempool_start_benchmark();
  redmule_synch_parallel(l1_X, K, l1_Wk, H * M, N, N, GEMM, SHIFT, PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Generate K", VERBOSE);

  /* Compute Q */
  mempool_start_benchmark();
  redmule_asynch_parallel(l1_X, Q, l1_Wq, H * M, N, N, GEMM, SHIFT, PORT_WIDTH);
  mempool_stop_benchmark();

  /* Transpose */
  mempool_start_benchmark();
  transpose_K(K, H, M, N, core_id, num_cores);
  mempool_stop_benchmark();

  /* Wait for RedMulE */
  mempool_start_benchmark();
  wait_redmule();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  /* Compute V */
  mempool_start_benchmark();
  redmule_synch_parallel(l1_X, V, l1_Wv, H * M, N, N, GEMM, SHIFT, PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Linear (I -> QKV) & Transposition", VERBOSE);

#else

  /* QKV generation */
  mempool_start_benchmark();

  redmule_asynch_parallel(l1_X, l1_Wq, Q, H * M, N, N, GEMM, SHIFT, PORT_WIDTH);
  wait_redmule();

  redmule_asynch_parallel(l1_X, l1_Wk, K, H * M, N, N, GEMM, SHIFT, PORT_WIDTH);
  wait_redmule();

  redmule_asynch_parallel(l1_X, l1_Wv, V, H * M, N, N, GEMM, SHIFT, PORT_WIDTH);
  wait_redmule();

  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  checkpoint_printf("Linear (I -> QKV)", VERBOSE);

  mempool_start_benchmark();
  transpose_K(K, H, M, N, core_id, num_cores);
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
      redmule_asynch_single(&Q[ih * (M * N)], &K[ih * (N * M)],
                            &A[ih * (M * M)], M, N, M, GEMM, redmule_id);
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
                            &l1_X[ih * (M * N)], M, M, N, GEMM, redmule_id);
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

  return 0;
}
