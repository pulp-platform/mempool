/*
 * Reduction DMA test (mesh-aware).
 *
 *   1. Every cluster's DM core loads the same reference pattern from HBM into
 *      its own l1_src — each cluster becomes a contributor with identical data.
 *   2. Cluster 0 issues a REDADD_UINT_16 reduction:
 *         dst = local(l1_result), src = remote_pos(self, l1_src), mask = 0/0.
 *      The collective NoC fans the read across the full
 *      ARCH_NUM_CLUSTER_X x ARCH_NUM_CLUSTER_Y mesh and accumulates each
 *      contributor's payload into the in-flight buffer before writing dst.
 *   3. Cluster 0 verifies l1_result[i] == (uint16_t)(N * l1_src[i]) where
 *      N = ARCH_NUM_CLUSTER, with uint16 wrap.
 *
 * Note: reduction OVERWRITES dst with sum(contributors). The destination
 * memory is NOT used as a seed value — pre-loading it has no effect on the
 * sum.
 *
 * Exercises FLEX_DMA_MODE_REDUCE (DMMASK + DMCPYC, collective_type = 2 =
 * REDADD_UINT_16) and the FlooNoC collective gather.
 */

#include "flex_runtime.h"
#include "flex_dma_pattern.h"
#include "flex_printf.h"
#include <stdint.h>

#define TRANSFER_ELEMS  32
#define TRANSFER_BYTES  (TRANSFER_ELEMS * sizeof(uint16_t))

/* Routing-mask cookbook (see floonoc_router.cpp::check_target):
 *   target <=> (cur & mask) == (src & mask) on each axis.
 *
 *   0x0000 → don't-care on every bit  → gather from every cluster on that axis
 *   0xFFFF → must match every bit     → only the source coordinate
 *   in-between → pin specific bits    → coset of source (e.g. 0x0001 = same parity) */
#define REDUCE_MASK_ALL       0x0000u   /* whole axis: every column / every row   */
#define REDUCE_MASK_SELF_ONLY 0xFFFFu   /* exact coordinate match: just one slice */

/* L1 offset of a TCDM symbol (TCDM base is 0, so this is just the address). */
#define L1_OFFSET(ptr)  ((uint32_t)(uintptr_t)(ptr))

/* L1 buffers replicated on every cluster */
static uint16_t l1_src   [TRANSFER_ELEMS] __attribute__((section(".l1"), aligned(64)));
static uint16_t l1_result[TRANSFER_ELEMS] __attribute__((section(".l1"), aligned(64)));

int main()
{
    uint32_t eoc_val = 0;
    flex_barrier_xy_init();
    flex_global_barrier_xy();
    if (flex_get_core_id() == 0 && flex_get_cluster_id() == 0) flex_timer_start();
    flex_global_barrier_xy();
    /**************************************/
    /*  Program Execution Region -- Start */
    /**************************************/

    const uint32_t cid = flex_get_cluster_id();

    /* Phase 1: every cluster pulls the same reference pattern from HBM. */
    if (flex_is_dm_core())
    {
        flex_dma_async_1d((uint64_t)(uintptr_t)l1_src, hbm_addr(0), TRANSFER_BYTES);
        flex_dma_async_wait_all();
    }

    /* Phase 2: ensure every contributor's l1_src is committed before the gather. */
    flex_global_barrier_xy();

    /* Phase 3: cluster 0 issues the full-mesh reduction. */
    if (flex_is_dm_core() && cid == 0)
    {
        printf("[Reduction] Mesh: %dx%d clusters, %u elems / %u bytes\n",
               ARCH_NUM_CLUSTER_X, ARCH_NUM_CLUSTER_Y,
               TRANSFER_ELEMS, (uint32_t)TRANSFER_BYTES);
        printf("[Reduction] Mask row=0x%04x col=0x%04x  (0x0000 = full fan-out)\n",
               REDUCE_MASK_ALL, REDUCE_MASK_ALL);
        printf("[Reduction] l1_src[0..3]:    0x%04x 0x%04x 0x%04x 0x%04x\n",
               l1_src[0], l1_src[1], l1_src[2], l1_src[3]);

        flex_dma_async_reduction(
            L1_OFFSET(l1_result),
            L1_OFFSET(l1_src),
            TRANSFER_BYTES,
            COLLECTIVE_REDADD_UINT_16,
            REDUCE_MASK_ALL, REDUCE_MASK_ALL);
        flex_dma_async_wait_all();

        printf("[Reduction] l1_result[0..3]: 0x%04x 0x%04x 0x%04x 0x%04x\n",
               l1_result[0], l1_result[1], l1_result[2], l1_result[3]);

        /* Phase 4: verify l1_result[i] == (uint16_t)(N * l1_src[i]) */
        const uint32_t n_contributors = ARCH_NUM_CLUSTER;
        uint32_t errors = 0;
        for (int i = 0; i < TRANSFER_ELEMS; ++i)
        {
            uint16_t expected = (uint16_t)(n_contributors * (uint32_t)l1_src[i]);
            if (l1_result[i] != expected)
            {
                if (errors < 4)
                    printf("  mismatch[%d]: got 0x%04x, expected 0x%04x\n",
                           i, l1_result[i], expected);
                errors++;
            }
        }
        printf("[Reduction] Verification: %s (%u errors out of %u, %u contributors)\n",
               errors == 0 ? "PASS" : "FAIL",
               errors, TRANSFER_ELEMS, n_contributors);
        eoc_val = errors;
    }

    /**************************************/
    /*  Program Execution Region -- Stop  */
    /**************************************/
    flex_global_barrier_xy();
    if (flex_get_core_id() == 0 && flex_get_cluster_id() == 0) flex_timer_end();
    flex_global_barrier_xy();
    flex_eoc(eoc_val);
    return 0;
}
