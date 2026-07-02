/*
 * Broadcast DMA test (mesh-aware).
 *
 * Cluster 0's DM core:
 *   1. Every cluster's DM core loads the same pattern from HBM into l1_src
 *      (used by each cluster as its own reference for verification).
 *   2. Cluster 0 issues a broadcast DMA: l1_src -> l1_dst
 *      Masks are derived from ARCH_NUM_CLUSTER_X / ARCH_NUM_CLUSTER_Y so the
 *      transfer fans out to every cluster in the configured mesh.
 *   3. Every cluster's DM core verifies its own l1_dst against l1_src and
 *      stores the local error count in l1_errors.
 *   4. Cluster 0 reads each cluster's error count via remote_cid and
 *      aggregates into the global eoc value.
 *
 * The test exercises:
 *   - FLEX_DMA_MODE_BCAST programming path in FlexMemPoolDmaCtrl
 *   - DMMASK + DMCPYC (collective_type = 1) forwarding to SnitchDma
 *   - Broadcast fan-out across the full ARCH_NUM_CLUSTER_X x ARCH_NUM_CLUSTER_Y mesh
 */

#include "flex_runtime.h"
#include "flex_dma_pattern.h"
#include "flex_printf.h"

#define TRANSFER_ELEMS  32          /* fp16 elements per transfer */
#define ELEM_BYTES      sizeof(uint16_t)
#define TRANSFER_BYTES  (TRANSFER_ELEMS * ELEM_BYTES)

/* Collective routing-mask cookbook (see floonoc_router.cpp::check_target):
 *   target <=> (cur & mask) == (src & mask) on each axis.
 *
 *   0x0000 → don't-care on every bit  → fan-out to every cluster on that axis
 *   0xFFFF → must match every bit     → only the source coordinate
 *   in-between → pin specific bits    → coset of source (e.g. 0x0001 = same parity) */
#define BCAST_MASK_ALL       0x0000u   /* whole axis: every column / every row   */
#define BCAST_MASK_SELF_ONLY 0xFFFFu   /* exact coordinate match: just one slice */

/* L1 buffers replicated on every cluster */
static uint16_t l1_src   [TRANSFER_ELEMS] __attribute__((section(".l1"), aligned(64)));
static uint16_t l1_dst   [TRANSFER_ELEMS] __attribute__((section(".l1"), aligned(64)));
static uint32_t l1_errors[1]             __attribute__((section(".l1"), aligned(64)));

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

    /* Step 1: every cluster pulls the reference pattern from HBM into its l1_src */
    if (flex_is_dm_core())
    {
        flex_dma_async_1d((uint64_t)(uintptr_t)l1_src, hbm_addr(0), TRANSFER_BYTES);
        flex_dma_async_wait_all();
        l1_errors[0] = 0;
    }

    /* Make sure every cluster has its reference loaded before the broadcast fires */
    flex_global_barrier_xy();

    /* Step 2: cluster 0 broadcasts to the full mesh */
    if (flex_is_dm_core() && cid == 0)
    {
        printf("[Broadcast] Mesh: %dx%d clusters, %u elems, %u bytes/transfer\n",
               ARCH_NUM_CLUSTER_X, ARCH_NUM_CLUSTER_Y,
               TRANSFER_ELEMS, (uint32_t)TRANSFER_BYTES);
        printf("[Broadcast] Source l1_src[0..3]: 0x%04x 0x%04x 0x%04x 0x%04x\n",
               l1_src[0], l1_src[1], l1_src[2], l1_src[3]);

        /* Fan-out to the full ARCH_NUM_CLUSTER_X x ARCH_NUM_CLUSTER_Y mesh */
        uint16_t row_mask = BCAST_MASK_ALL;   /* X axis: hit every column */
        uint16_t col_mask = BCAST_MASK_ALL;   /* Y axis: hit every row    */

        /* The broadcast engine rewrites the cluster index inside the TCDM remote
         * alias for every mask bit, so the destination must be expressed as
         * remote_pos(self, offset) rather than a plain local L1 address. */
        const uint32_t dst_offset =
            (uint32_t)((uintptr_t)l1_dst - (uintptr_t)local(0));
        const uint32_t src_offset =
            (uint32_t)((uintptr_t)l1_src - (uintptr_t)local(0));
        FlexPosition self_pos = get_pos(cid);

        bare_dma_start_1d_broadcast(
            (uint64_t)remote_pos(self_pos, dst_offset),
            (uint64_t)local(src_offset),
            TRANSFER_BYTES,
            row_mask, col_mask
        );
        flex_dma_async_wait_all();
    }

    /* Wait until the broadcast has landed in every cluster's L1 */
    flex_global_barrier_xy();

    /* Step 3: each cluster verifies its own l1_dst against the reference l1_src */
    if (flex_is_dm_core())
    {
        uint32_t errors = 0;
        for (int i = 0; i < TRANSFER_ELEMS; ++i)
        {
            if (l1_dst[i] != l1_src[i]) errors++;
        }
        l1_errors[0] = errors;
    }

    /* Publish per-cluster results before cluster 0 collects them */
    flex_global_barrier_xy();

    /* Step 4: cluster 0 aggregates per-cluster error counts via remote DMA */
    if (flex_is_dm_core() && cid == 0)
    {
        const uint32_t err_offset =
            (uint32_t)((uintptr_t)l1_errors - (uintptr_t)local(0));
        uint32_t remote_err = 0;
        uint32_t total_errors = l1_errors[0];
        uint32_t failing_clusters = (l1_errors[0] != 0) ? 1u : 0u;

        printf("[Broadcast] After bcast, cluster 0 l1_dst[0..3]: "
               "0x%04x 0x%04x 0x%04x 0x%04x\n",
               l1_dst[0], l1_dst[1], l1_dst[2], l1_dst[3]);

        for (uint32_t rid = 1; rid < ARCH_NUM_CLUSTER; ++rid)
        {
            flex_dma_async_1d(
                (uint64_t)(uintptr_t)&remote_err,
                (uint64_t)remote_cid(rid, err_offset),
                sizeof(remote_err));
            flex_dma_async_wait_all();

            if (remote_err) failing_clusters++;
            total_errors += remote_err;
        }

        printf("[Broadcast] Verification: %s "
               "(%u total errors, %u/%u clusters failed)\n",
               total_errors == 0 ? "PASS" : "FAIL",
               total_errors, failing_clusters, (uint32_t)ARCH_NUM_CLUSTER);
        eoc_val = total_errors;
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
