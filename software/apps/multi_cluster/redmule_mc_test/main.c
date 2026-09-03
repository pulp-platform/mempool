/*
 * Minimal RedMulE-on-multi-cluster isolation test, per the user's request:
 * every cluster independently runs a plain matmul on its own local RedMulE
 * tiles, using redmule_synch_parallel() (the pre-existing, proven wrapper
 * from baremetal/mempool_redmule_f16.h -- which already bakes in the
 * mempool_barrier(num_cores) call after the RedMulE trigger, unlike
 * conv1d_f16's own inline usage). No DMA, no cross-cluster data movement,
 * no im2col -- purely "does a RedMulE job issued from every cluster in a
 * multi-cluster grid actually complete".
 */

#include "mc_dma_pattern.h"
#include "mc_printf.h"
#include "mc_runtime.h"
#include <string.h>

#include "archi_redmule.h"
#include "hal_redmule.h"
#include "baremetal/mempool_redmule_f16.h"

#define M (16)
#define N (16)
#define P (16)

static __fp16 l1_X[M][N] __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_W[N][P] __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_Y[M][P] __attribute__((section(".l1"), aligned(64)));

static inline void bits_fp16(uint16_t u, __fp16 *x) { memcpy(x, &u, sizeof(u)); }
#define ONE_FP16_BITS (0x3c00) /* 1.0 in IEEE-754 half */

#define DONE(label)                                                          \
  do {                                                                       \
    if (core_id == 0 && cluster_id == 0) {                                   \
      printf("/* DONE: %s */\n", (label));                                   \
    }                                                                        \
    mc_global_barrier_xy();                                                  \
  } while (0)

int main() {
  uint32_t eoc_val = 0;
  uint32_t core_id = mc_get_core_id();
  uint32_t cluster_id = mc_get_cluster_id();

  if (core_id == 0 && cluster_id == 0) {
    printf("[Cluster 0] entered main\n");
  }

  mc_barrier_xy_init();
  mc_global_barrier_xy();
  DONE("after first mc_global_barrier_xy");

  /* Every cluster fills its own local X (identity-like, zero elsewhere) and
   * W (identity), so Y should end up equal to X: a simple, cheap
   * correctness check alongside the "did it hang" check. */
  if (mc_is_dm_core()) {
    memset(l1_X, 0, sizeof(l1_X));
    memset(l1_W, 0, sizeof(l1_W));
    memset(l1_Y, 0, sizeof(l1_Y));
    for (uint32_t i = 0; i < M && i < N; ++i) {
      bits_fp16(ONE_FP16_BITS, &l1_X[i][i]);
    }
    for (uint32_t i = 0; i < N && i < P; ++i) {
      bits_fp16(ONE_FP16_BITS, &l1_W[i][i]);
    }
  }
  mc_global_barrier_xy();
  DONE("Generate inputs");

  redmule_synch_parallel(&l1_X[0][0], &l1_W[0][0], &l1_Y[0][0], M, N, P, GEMM,
                         false, 0);
  mc_global_barrier_xy();
  DONE("RedMulE matmul");

  if (mc_is_dm_core()) {
    uint32_t errors = 0;
    for (uint32_t i = 0; i < M; ++i) {
      for (uint32_t j = 0; j < P; ++j) {
        uint16_t expected = (i == j && i < N) ? ONE_FP16_BITS : 0x0000;
        uint16_t got;
        memcpy(&got, &l1_Y[i][j], sizeof(got));
        if (got != expected) {
          if (errors < 4) {
            printf("[Cluster %u] mismatch i=%u j=%u: got 0x%04x expected "
                   "0x%04x\n",
                   cluster_id, i, j, got, expected);
          }
          ++errors;
        }
      }
    }
    printf("[Cluster %u] RedMulE matmul check: %s (%u mismatches)\n",
           cluster_id, errors == 0 ? "PASS" : "FAIL", errors);
    eoc_val += errors;
  }

  mc_global_barrier_xy();
  mc_eoc(eoc_val);
  return 0;
}
