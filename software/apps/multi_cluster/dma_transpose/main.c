/*
 * 2D DMA test: transpose the first two dimensions of an L1-resident tensor,
 * writing the DMA result directly into cluster 1's L1 (cluster 0 -> cluster
 * 1), while the core version stays a local, intra-cluster-0 transpose for
 * comparison.
 *
 * Source layout (cluster 0's L1):
 *   l1_src[m][n][p]   with shape [M][N][P]
 *
 * Transfer goal:
 *   dst[n][m][p] = l1_src[m][n][p]  for all valid indices,
 *   where dst = l1_dma_dst living in CLUSTER 1's L1 for the DMA path,
 *   and   dst = l1_core_dst living in cluster 0's own L1 for the core path.
 *
 * For each fixed n, a single 2D DMA copies M rows of width P elements from
 * cluster 0's l1_src into cluster 1's l1_dma_dst, addressed via remote_cid():
 *   src  = &l1_src[0][n][0]                      (local to cluster 0)
 *   dst  = remote_cid(1, offset of l1_dst[n][0][0]) (cluster 1's L1)
 *   size = P * sizeof(uint16_t)
 *   src_stride = N * P * sizeof(uint16_t)
 *   dst_stride = P * sizeof(uint16_t)
 *   reps = M
 *
 * After the timed transfer, cluster 0 DMA's the result back from cluster 1
 * into a local readback buffer purely so it can verify the transfer -- that
 * readback is intentionally outside the timed region.
 */

#include "mc_dma_pattern.h"
#include "mc_printf.h"
#include "mc_runtime.h"
#include <string.h>

#define M 4
#define N 64
#define P 16

static uint16_t l1_src[M][N][P] __attribute__((section(".l1"), aligned(64)));
/* Lives in every cluster's L1 at the same local address; its role changes
 * per phase -- cluster 0's core-transpose output, then cluster 1's real DMA
 * write target, then cluster 0's local readback landing zone. */
static uint16_t l1_dst[N][M][P] __attribute__((section(".l1"), aligned(64)));

int main() {
  uint32_t eoc_val = 0;

  mc_barrier_xy_init();
  mc_global_barrier_xy();

  /**************************************/
  /*  Initialization                    */
  /**************************************/

  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {
    for (uint32_t m = 0; m < M; ++m) {
      for (uint32_t n = 0; n < N; ++n) {
        for (uint32_t p = 0; p < P; ++p) {
          l1_src[m][n][p] = (uint16_t)((m << 12) | (n << 4) | p);
        }
      }
    }
    memset(l1_dst, 0, sizeof(l1_dst));
  }

  /* Cluster 1 clears its own copy of l1_dst. */
  if (mc_is_dm_core() && mc_get_cluster_id() == 1) {
    memset(l1_dst, 0, sizeof(l1_dst));
    printf("[Core transpose] finished initialization\n");
  }

  mc_global_barrier_xy();

  /**************************************/
  /*  Program Execution Region -- Start */
  /**************************************/

  if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0) {
    mc_timer_start();
  }

  if (mc_get_cluster_id() == 0) {
    const uint32_t core_id = mc_get_core_id();
    const uint32_t num_cores = mempool_get_core_count();
    uint16_t *dst = &l1_dst[0][0][0];
    const uint16_t *src = &l1_src[0][0][0];

    for (uint32_t idx = core_id; idx < M * N; idx += num_cores) {
      const uint32_t i = idx / N;
      const uint32_t j = idx % N;
      for (uint32_t k = 0; k < P; ++k) {
        const uint32_t src_idx = (i * N + j) * P + k;
        const uint32_t dst_idx = (j * M + i) * P + k;
        dst[dst_idx] = src[src_idx];
      }
    }
  }

  mc_intra_cluster_sync();

  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {
    /* Offset of l1_dst within L1, reinterpreted against cluster 1's L1
     * base by remote_cid() -- this is what makes the write land in cluster
     * 1 instead of cluster 0's own L1. */
    const uint32_t dst_base_offset =
        (uint32_t)((uintptr_t)&l1_dst[0][0][0] - (uintptr_t)local(0));
    mc_dma_sync_1d((uint64_t)remote_cid(1, dst_base_offset),
                  (uint64_t)(uintptr_t)&l1_dst[0][0][0], sizeof(l1_dst));
  }

  mc_global_barrier_xy();
  if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0) {
    mc_timer_end();
    printf("[Core transpose] timing end\n");
  }
  mc_global_barrier_xy();

  /**************************************/
  /*  Check                             */
  /**************************************/

  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {
    uint32_t errors = 0;

    for (uint32_t m = 0; m < M; ++m) {
      for (uint32_t n = 0; n < N; ++n) {
        for (uint32_t p = 0; p < P; ++p) {
          const uint16_t expected = l1_src[m][n][p];
          const uint16_t obtained = l1_dst[n][m][p];
          if (obtained != expected) {
            if (errors < 4) {
              printf("[Core transpose] mismatch m=%u n=%u p=%u: got 0x%04x "
                     "expected 0x%04x\n",
                     m, n, p, obtained, expected);
            }
            ++errors;
          }
        }
      }
    }

    printf("[Core transpose] Verification: %s (%u errors)\n",
           errors == 0 ? "PASS" : "FAIL", errors);
    eoc_val += errors;
  }
  mc_global_barrier_xy();

  /**************************************/
  /*  Initialization                    */
  /**************************************/

  /* Cluster 0 clears its own copy of l1_dst. */
  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {
    memset(l1_dst, 0, sizeof(l1_dst));
  }

  /* Cluster 1 clears its own copy of l1_dst. */
  if (mc_is_dm_core() && mc_get_cluster_id() == 1) {
    memset(l1_dst, 0, sizeof(l1_dst));
    printf("[DMA transpose] finished initialization\n");
  }

  mc_global_barrier_xy();

  /**************************************/
  /*  Program Execution Region -- Start */
  /**************************************/

  if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0) {
    mc_timer_start();
  }

  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {

    const size_t row_bytes = P * sizeof(uint16_t);
    const size_t src_stride = N * row_bytes;
    const size_t dst_stride = row_bytes;
    /* Offset of l1_dst within L1, reinterpreted against cluster 1's L1
     * base by remote_cid() -- this is what makes the write land in cluster
     * 1 instead of cluster 0's own L1. */
    const uint32_t dst_base_offset =
        (uint32_t)((uintptr_t)&l1_dst[0][0][0] - (uintptr_t)local(0));

    for (uint32_t n = 0; n < N; ++n) {
      const uint32_t dst_offset =
          dst_base_offset + n * (uint32_t)sizeof(l1_dst[0]);
      mc_dma_sync_2d((uint64_t)remote_cid(1, dst_offset),
                     (uint64_t)(uintptr_t)&l1_src[0][n][0], row_bytes,
                     dst_stride, src_stride, M);
    }
  }

  mc_global_barrier_xy();
  if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0) {
    mc_timer_end();
    printf("[DMA transpose] timing end\n");
  }
  mc_global_barrier_xy();

  /**************************************/
  /*  Check                             */
  /**************************************/

  /*  Read back cluster 1's result for verification (untimed) */
  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {
    const uint32_t dst_base_offset =
        (uint32_t)((uintptr_t)&l1_dst[0][0][0] - (uintptr_t)local(0));
    mc_dma_async_1d((uint64_t)(uintptr_t)l1_dst,
                    (uint64_t)remote_cid(1, dst_base_offset),
                    sizeof(l1_dst));
    mc_dma_async_wait_all();
  }

  mc_global_barrier_xy();

  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {
    uint32_t errors = 0;

    for (uint32_t m = 0; m < M; ++m) {
      for (uint32_t n = 0; n < N; ++n) {
        for (uint32_t p = 0; p < P; ++p) {
          const uint16_t expected = l1_src[m][n][p];
          const uint16_t obtained = l1_dst[n][m][p];

          if (obtained != expected) {
            if (errors < 4) {
              printf("[DMA transpose] mismatch m=%u n=%u p=%u: got 0x%04x "
                     "expected 0x%04x\n",
                     m, n, p, obtained, expected);
            }
            ++errors;
          }
        }
      }
    }

    printf("[DMA transpose] Verification: %s (%u errors)\n",
           errors == 0 ? "PASS" : "FAIL", errors);
    eoc_val += errors;
  }

  /**************************************/
  /*  Program Execution Region -- Stop  */
  /**************************************/

  mc_global_barrier_xy();
  mc_eoc(eoc_val);
  return 0;
}
