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

#include "baremetal/mempool_softmax_f16.h"
#include "baremetal/redmule_f16.h"

#define H (4)
#define M (128)
#define N (512)

#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))
#define SHIFT (true)
#define VERBOSE (true)

__fp16 l2_I[H * M * N]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l2")));
__fp16 l2_W[3 * H * M * H * M]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l2")));

#if !(DOUBLE_BUFFERING)
__fp16 l1_I[H * M * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_W[3 * H * M * H * M]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_QKV[3 * H * M * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#else
__fp16 l1_I[H * M * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_W[H * M * H * M]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_QKV[3 * H * M * N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#endif

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

#ifdef DOUBLE_BUFFERING

int main() {

  /* Initialization */
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  /* L1 transfer */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l1_I, l2_I, (H * M * N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_W, l2_W, 3 * (H * M * H * M) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Transfer-in                                     */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* Allocate */
  static __fp16 *Q = l1_QKV;
  static __fp16 *K = &l1_QKV[2 * H * M * N];
  static __fp16 *V = &l1_QKV[2 * H * M * N];

  /* Generate K */
  mempool_start_benchmark();
  redmule_synch_parallel(l1_I, l1_QKV, l1_W,
    H * M, H * M, N, GEMM, SHIFT, PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Generate K                                      */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* Compute Q */
  mempool_start_benchmark();
  redmule_asynch_parallel(l1_I, l1_QKV, l1_W,
    H * M, H * M, N, GEMM, SHIFT, PORT_WIDTH);
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
  redmule_synch_parallel(l1_I, l1_QKV, l1_W,
    H * M, H * M, N, GEMM, SHIFT, PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Linear (I -> QKV) & Transposition               */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* The rest is the same as in the non double-buffered case */
  return 0;
}

#else

int main() {

  /* Initialization */
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  /* L1 transfer */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l1_I, l2_I, (H * M * N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_W, l2_W, (3 * H * M * H * M) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Transfer-in                                     */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* QKV generation */
  mempool_start_benchmark();
  for (uint32_t i = 0; i < 3; i++) {
    redmule_asynch_parallel(l1_W, l1_QKV, l1_I,
      H * M, H * M, N, GEMM, SHIFT, PORT_WIDTH);
    wait_redmule();
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Linear (I -> QKV)                               */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* Allocate */
  static __fp16 *Q = l1_QKV;
  static __fp16 *K = &l1_QKV[1 * H * M * N];
  static __fp16 *V = &l1_QKV[2 * H * M * N];

  /* Transpose K */
  mempool_start_benchmark();
  transpose_K(K, H, M, N, core_id, num_cores);
  mempool_stop_benchmark();

  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Transpose                                       */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* Q and W are not reused */
  static __fp16 *A = l1_W;
  static __fp16 *smA = l1_QKV;

  /* A = Q * Kt */
  mempool_start_benchmark();
  uint32_t ih = redmule_id / H;
  redmule_synch_parallel(Q, A, K + ih * (N * M),
    H * M, N, M, GEMM, SHIFT, PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Q * Kt                                          */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* Softmax */
  mempool_start_benchmark();
  __fp16 *I_ptr = A;
  __fp16 *O_ptr = smA;
  softmax_parallel_2x4_f16vec(I_ptr, O_ptr, H * M, M, core_id, num_cores);
  mempool_stop_benchmark();

  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Softmax                                         */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* A * V */
  mempool_start_benchmark();
  uint32_t ih = redmule_id / H;
  redmule_synch_parallel(A, l1_I, V + ih * (M * N),
    H * M, N, M, GEMM, SHIFT, PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Softmax(A) * V                                  */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /* L1 transfer */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l2_I, l1_I, (H * M * N) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Transfer-out                                    */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  return 0;
}

#endif
