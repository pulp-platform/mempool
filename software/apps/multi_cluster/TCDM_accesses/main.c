#include "flex_runtime.h"
#include "flex_dma_pattern.h"
#include "flex_printf.h"

#define NUM_ELEMS 16

static uint32_t l1_src_pattern[NUM_ELEMS] __attribute__((section(".l1"), aligned(64)));
static uint32_t l1_remote_results[ARCH_NUM_CLUSTER + 2][NUM_ELEMS] __attribute__((section(".l1"), aligned(64)));

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

    uint32_t cid = flex_get_cluster_id();

    /* ---- Phase 1: each cluster writes a pattern into its own L1 TCDM ---- */
    if (flex_is_dm_core())
    {
        volatile uint32_t * local_ptr = (volatile uint32_t *)l1_src_pattern;
        for (int i = 0; i < NUM_ELEMS; ++i)
            local_ptr[i] = (cid << 16) | i;
        
        if (cid == 0){
            printf("[Cluster %d] Wrote local pattern: 0x%08x .. 0x%08x\n", cid, local_ptr[0], local_ptr[NUM_ELEMS - 1]);
        }
    }

    /* Synchronize so every cluster's data is committed */
    flex_global_barrier_xy();

    /* ---- Phase 2: cluster 0 reads from every remote cluster via DMA ---- */
    if (flex_is_dm_core() && cid == 0)
    {
        uint32_t transfer_size = sizeof(l1_src_pattern);
        uint32_t src_offset = (uint32_t)((uintptr_t)l1_src_pattern - (uintptr_t)local(0));

        for (uint32_t remote_id = 0; remote_id < ARCH_NUM_CLUSTER; ++remote_id)
        {
            /* DMA: remote cluster TCDM -> local L1 result buffer */
            volatile uint32_t *buf = (volatile uint32_t *)l1_remote_results[remote_id];
            flex_dma_async_1d(
                (uint64_t)(uintptr_t)buf,
                (uint64_t)remote_cid(remote_id, src_offset),
                transfer_size);
            flex_dma_async_wait_all();

            printf("[Cluster 0] Read from cluster %d (remote_cid): first=0x%08x last=0x%08x\n",
                   remote_id, buf[0], buf[NUM_ELEMS - 1]);
        }

        /* Also demonstrate remote_xy: read cluster at (1,0) */
        volatile uint32_t *xy_buf = (volatile uint32_t *)l1_remote_results[ARCH_NUM_CLUSTER];
        flex_dma_async_1d(
            (uint64_t)(uintptr_t)xy_buf,
            (uint64_t)remote_xy(1, 0, src_offset),
            transfer_size);
        flex_dma_async_wait_all();

        printf("[Cluster 0] Read via remote_xy(1,0): first=0x%08x last=0x%08x\n",
               xy_buf[0], xy_buf[NUM_ELEMS - 1]);

        /* Also demonstrate remote_pos: read cluster at position (0,1) */
        FlexPosition target_pos;
        target_pos.x = 0;
        target_pos.y = 1;
        volatile uint32_t *pos_buf = (volatile uint32_t *)l1_remote_results[ARCH_NUM_CLUSTER + 1];
        flex_dma_async_1d(
            (uint64_t)(uintptr_t)pos_buf,
            (uint64_t)remote_pos(target_pos, src_offset),
            transfer_size);
        flex_dma_async_wait_all();

        printf("[Cluster 0] Read via remote_pos(0,1): first=0x%08x last=0x%08x\n",
               pos_buf[0], pos_buf[NUM_ELEMS - 1]);
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
