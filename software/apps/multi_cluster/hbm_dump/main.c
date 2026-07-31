#include "mc_runtime.h"
#include "mc_dma_pattern.h"
#include "mc_printf.h"
#include "mc_dump.h"

#define HBM_TRANSFER_ELEMS (64 * 64)
static uint16_t l1_dma_buffer[HBM_TRANSFER_ELEMS] __attribute__((section(".l1"), aligned(64)));


int main()
{
    uint32_t eoc_val = 0;
    mc_barrier_xy_init();
    mc_global_barrier_xy();
    if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0) mc_timer_start();
    mc_global_barrier_xy();
    /**************************************/
    /*  Program Execution Region -- Start */
    /**************************************/

    uint64_t A_matrix_in_HBM_offset = 0;
    uint32_t transfer_size = sizeof(l1_dma_buffer);
    if (mc_is_dm_core() && (mc_get_cluster_id() == 0))
    {
        volatile uint16_t * local_ptr = (volatile uint16_t *)l1_dma_buffer;
        printf("[Before load HBM to L1] the first 8 elements of local L1 buffer are:\n");
        for (int i = 0; i < 8; ++i)
        {
            printf("    0x%04x\n", local_ptr[i]);
        }

        mc_dma_async_1d((uint64_t)(uintptr_t)l1_dma_buffer, hbm_addr(A_matrix_in_HBM_offset), transfer_size);
        printf("[Now    load HBM to L1] loading with asynchronize API\n");
        mc_dma_async_wait_all();

        printf("[After  load HBM to L1] the first 8 elements of local L1 buffer are:\n");
        for (int i = 0; i < 8; ++i)
        {
            printf("    0x%04x\n", local_ptr[i]);
        }

        uint64_t destination_in_HBM_offest = 4 * transfer_size;
        mc_dma_async_1d(hbm_addr(destination_in_HBM_offest), (uint64_t)(uintptr_t)l1_dma_buffer, transfer_size);
        printf("[Now    store L1 to HBM] storing with asynchronize API\n");
        mc_dma_async_wait_all();

        printf("[Dump  HBM data to File]\n");
        mc_dump_open();
        mc_dump_hbm(A_matrix_in_HBM_offset, transfer_size);
        mc_dump_hbm(destination_in_HBM_offest, transfer_size);
        mc_dump_close();
    }

    /**************************************/
    /*  Program Execution Region -- Stop  */
    /**************************************/
    mc_global_barrier_xy();
    if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0) mc_timer_end();
    mc_global_barrier_xy();
    mc_eoc(eoc_val);
    return 0;
}
