/*
 * 2D DMA test: strided load from HBM into L1.
 *
 * HBM layout (fp16, row-major):
 *   Matrix A: ROWS rows, COLS_HBM columns  (all columns present in HBM)
 *
 * Transfer goal: load only the first COLS_LOAD columns of each row into L1.
 *   src_stride = COLS_HBM * sizeof(uint16_t)  — jump a full HBM row between reps
 *   dst_stride = COLS_LOAD * sizeof(uint16_t) — pack loaded elements tightly in L1
 *   size       = COLS_LOAD * sizeof(uint16_t) — bytes copied per repetition
 *   reps       = ROWS                          — one rep per HBM row
 *
 * Expected L1 content after DMA:
 *   l1_buf[r][c] == HBM[r][c]  for 0 <= r < ROWS, 0 <= c < COLS_LOAD
 */

#include "flex_runtime.h"
#include "flex_dma_pattern.h"
#include "flex_printf.h"

#define ROWS       4                /* number of rows to load              */
#define COLS_HBM   64               /* full row width in HBM (fp16 elems)  */
#define COLS_LOAD  16               /* columns to load per row             */
#define ELEM_BYTES sizeof(uint16_t)

/* L1 destination: ROWS × COLS_LOAD fp16 matrix, packed tightly (row-major) */
static uint16_t l1_buf[ROWS][COLS_LOAD] __attribute__((section(".l1"), aligned(64)));

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

    if (flex_is_dm_core() && flex_get_cluster_id() == 0)
    {
        printf("[2D DMA] Before transfer — l1_buf[0][0..3]: 0x%04x 0x%04x 0x%04x 0x%04x\n",
               l1_buf[0][0], l1_buf[0][1], l1_buf[0][2], l1_buf[0][3]);

        const size_t row_bytes  = sizeof(l1_buf[0]);     /* COLS_LOAD * ELEM_BYTES  */
        const size_t src_stride = COLS_HBM * ELEM_BYTES; /* HBM row pitch           */
        const size_t dst_stride = sizeof(l1_buf[0]);     /* L1 row pitch (packed)   */

        flex_dma_async_2d(
            (uint64_t)(uintptr_t)l1_buf,  /* dst: L1 matrix base              */
            hbm_addr(0),                  /* src: start of HBM matrix A       */
            row_bytes,                    /* size per rep                     */
            dst_stride,                   /* dst stride between reps          */
            src_stride,                   /* src stride between reps          */
            ROWS                          /* number of repetitions            */
        );

        flex_dma_async_wait_all();

        printf("[2D DMA] After  transfer — first/last element of each loaded row:\n");
        for (int r = 0; r < ROWS; ++r)
        {
            printf("  row %d: 0x%04x 0x%04x ... 0x%04x\n",
                   r,
                   l1_buf[r][0],
                   l1_buf[r][1],
                   l1_buf[r][COLS_LOAD - 1]);
        }
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
