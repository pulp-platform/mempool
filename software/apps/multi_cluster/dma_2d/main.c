/*
 * 2D DMA test: strided load from HBM into L1.
 *
 * HBM layout (fp16, row-major):
 *   Matrix A: ROWS rows, COLS_HBM columns  (all columns present in HBM)
 *
 * Transfer goal: load only the first COLS_LOAD columns of each row into L1.
 *   src_stride = COLS_HBM * sizeof(uint16_t)  — jump a full HBM row between
 * reps dst_stride = COLS_LOAD * sizeof(uint16_t) — pack loaded elements tightly
 * in L1 size       = COLS_LOAD * sizeof(uint16_t) — bytes copied per repetition
 *   reps       = ROWS                          — one rep per HBM row
 *
 * Expected L1 content after DMA:
 *   l1_buf[r][c] == HBM[r][c]  for 0 <= r < ROWS, 0 <= c < COLS_LOAD
 */

#include "mc_dma_pattern.h"
#include "mc_printf.h"
#include "mc_runtime.h"
#include <string.h>

#define ROWS 4       /* number of rows to load              */
#define COLS_HBM 64  /* full row width in HBM (fp16 elems)  */
#define COLS_LOAD 16 /* columns to load per row             */
#define ELEM_BYTES sizeof(uint16_t)

/* L1 source used to seed the HBM test pattern before loading it back. */
static uint16_t hbm_init[ROWS][COLS_HBM]
    __attribute__((section(".l1"), aligned(64)));

/* L1 destination: ROWS × COLS_LOAD fp16 matrix, packed tightly (row-major) */
static uint16_t l1_buf[ROWS][COLS_LOAD]
    __attribute__((section(".l1"), aligned(64)));

int main() {
  uint32_t eoc_val = 0;
  mc_barrier_xy_init();
  mc_global_barrier_xy();
  if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0)
    mc_timer_start();
  mc_global_barrier_xy();

  /**************************************/
  /*  Program Execution Region -- Start */
  /**************************************/

  if (mc_is_dm_core() && mc_get_cluster_id() == 0) {

    /*  Initialize  */

    for (int r = 0; r < ROWS; ++r) {
      for (int c = 0; c < COLS_HBM; ++c) {
        hbm_init[r][c] = (uint16_t)((r << 8) | c);
      }
    }

    mc_dma_async_1d(hbm_addr(0), (uint64_t)(uintptr_t)hbm_init,
                    sizeof(hbm_init));
    mc_dma_async_wait_all();

    memset(l1_buf, 0, sizeof(l1_buf));

    printf("[2D DMA] Before transfer — hbm_init[0][0..3]:\n");
    for (int r = 0; r < ROWS; ++r) {
      uint16_t v0 = hbm_init[r][0];
      uint16_t v1 = hbm_init[r][1];
      uint16_t v2 = hbm_init[r][COLS_LOAD - 1];
      printf("  row %d: 0x%04x 0x%04x ... 0x%04x\n", r, v0, v1, v2);
    }

    /*  Transfer  */

    const size_t row_bytes = sizeof(l1_buf[0]); /* COLS_LOAD * ELEM_BYTES  */
    const size_t src_stride = COLS_HBM * ELEM_BYTES; /* HBM row pitch */
    const size_t dst_stride = sizeof(l1_buf[0]); /* L1 row pitch (packed)   */

    mc_dma_async_2d((uint64_t)(uintptr_t)l1_buf, /* dst: L1 matrix base */
                    hbm_addr(0), /* src: start of HBM matrix A       */
                    row_bytes,   /* size per rep                     */
                    dst_stride,  /* dst stride between reps          */
                    src_stride,  /* src stride between reps          */
                    ROWS         /* number of repetitions            */
    );

    mc_dma_async_wait_all();

    printf(
        "[2D DMA] After  transfer — first/last element of each loaded row:\n");
    for (int r = 0; r < ROWS; ++r) {
      uint16_t v0 = l1_buf[r][0];
      uint16_t v1 = l1_buf[r][1];
      uint16_t v2 = l1_buf[r][COLS_LOAD - 1];
      printf("  row %d: 0x%04x 0x%04x ... 0x%04x\n", r, v0, v1, v2);
    }
  }

  mc_global_barrier_xy();

  if (mc_is_dm_core() && mc_get_cluster_id() == 1) {

    const uint32_t src_offset =
        (uint32_t)((uintptr_t)l1_buf - (uintptr_t)local(0));

    mc_dma_async_1d((uint64_t)(uintptr_t)l1_buf,
                    (uint64_t)remote_cid(0, src_offset), sizeof(l1_buf));
    mc_dma_async_wait_all();

    printf(
        "[Cluster 1] Tile from cluster 0 — first/last element of each row:\n");
    for (int r = 0; r < ROWS; ++r) {
      uint16_t v0 = l1_buf[r][0];
      uint16_t v1 = l1_buf[r][1];
      uint16_t v2 = l1_buf[r][COLS_LOAD - 1];
      printf("  row %d: 0x%04x 0x%04x ... 0x%04x\n", r, v0, v1, v2);
    }
  }

  /**************************************/
  /*  Program Execution Region -- Stop  */
  /**************************************/

  mc_global_barrier_xy();
  if (mc_get_core_id() == 0 && mc_get_cluster_id() == 0)
    mc_timer_end();
  mc_global_barrier_xy();
  mc_eoc(eoc_val);
  return 0;
}
