#ifndef _FLEX_DMA_PATTERN_H_
#define _FLEX_DMA_PATTERN_H_

#include "flex_runtime.h"
#include "flex_cluster_arch.h"
#include <stddef.h>
#include <stdint.h>

#ifndef ARCH_CLUSTER_DMA_CTRL_BASE
#define ARCH_CLUSTER_DMA_CTRL_BASE 0x40010000u
#endif

/********************************************
*  iDMA CSR shim (MemPool-fashion MMIO)     *
********************************************/

// Word offsets in the CSR bank at ARCH_CLUSTER_DMA_CTRL_BASE.
#define FLEX_DMA_REG_SRC_LO       0
#define FLEX_DMA_REG_SRC_HI       1
#define FLEX_DMA_REG_DST_LO       2
#define FLEX_DMA_REG_DST_HI       3
#define FLEX_DMA_REG_SIZE         4
#define FLEX_DMA_REG_SRC_STRIDE   5
#define FLEX_DMA_REG_DST_STRIDE   6
#define FLEX_DMA_REG_REPS         7
#define FLEX_DMA_REG_MASK         8
#define FLEX_DMA_REG_REDUCT_FMT   9
#define FLEX_DMA_REG_MODE         10
#define FLEX_DMA_REG_LAUNCH       11
#define FLEX_DMA_REG_STATUS       12

#define FLEX_DMA_MODE_1D       0u
#define FLEX_DMA_MODE_2D       1u
#define FLEX_DMA_MODE_BCAST    2u
#define FLEX_DMA_MODE_REDUCE   3u

typedef enum {
    COLLECTIVE_REDADD_UINT_16,
    COLLECTIVE_REDADD_INT_16,
    COLLECTIVE_REDADD_FP_16,
    COLLECTIVE_REDMAX_UINT_16,
    COLLECTIVE_REDMAX_INT_16,
    COLLECTIVE_REDMAX_FP_16
} collective_compute_format_t;

static inline volatile uint32_t *flex_dma_csr(void) {
    return (volatile uint32_t *)ARCH_CLUSTER_DMA_CTRL_BASE;
}

static inline void flex_dma_program_addr(uint64_t dst, uint64_t src, size_t size) {
    volatile uint32_t *d = flex_dma_csr();
    d[FLEX_DMA_REG_SRC_LO] = (uint32_t)(src);
    d[FLEX_DMA_REG_SRC_HI] = (uint32_t)(src >> 32);
    d[FLEX_DMA_REG_DST_LO] = (uint32_t)(dst);
    d[FLEX_DMA_REG_DST_HI] = (uint32_t)(dst >> 32);
    d[FLEX_DMA_REG_SIZE]   = (uint32_t)size;
}

inline uint32_t bare_dma_start_1d(uint64_t dst, uint64_t src, size_t size) {
    volatile uint32_t *d = flex_dma_csr();
    flex_dma_program_addr(dst, src, size);
    d[FLEX_DMA_REG_MODE] = FLEX_DMA_MODE_1D;
    __sync_synchronize();
    uint32_t tx_id = d[FLEX_DMA_REG_LAUNCH];
    __sync_synchronize();
    return tx_id;
}

inline uint32_t bare_dma_start_2d(uint64_t dst, uint64_t src, size_t size,
                                  size_t dst_stride, size_t src_stride, size_t repeat) {
    volatile uint32_t *d = flex_dma_csr();
    flex_dma_program_addr(dst, src, size);
    d[FLEX_DMA_REG_SRC_STRIDE] = (uint32_t)src_stride;
    d[FLEX_DMA_REG_DST_STRIDE] = (uint32_t)dst_stride;
    d[FLEX_DMA_REG_REPS]       = (uint32_t)repeat;
    d[FLEX_DMA_REG_MODE]       = FLEX_DMA_MODE_2D;
    __sync_synchronize();
    uint32_t tx_id = d[FLEX_DMA_REG_LAUNCH];
    __sync_synchronize();
    return tx_id;
}

inline uint32_t bare_dma_start_1d_broadcast(uint64_t dst, uint64_t src, size_t size,
                                            uint16_t row_mask, uint16_t col_mask) {
    volatile uint32_t *d = flex_dma_csr();
    flex_dma_program_addr(dst, src, size);
    d[FLEX_DMA_REG_MASK] = ((uint32_t)col_mask << 16) | (uint32_t)row_mask;
    d[FLEX_DMA_REG_MODE] = FLEX_DMA_MODE_BCAST;
    __sync_synchronize();
    uint32_t tx_id = d[FLEX_DMA_REG_LAUNCH];
    __sync_synchronize();
    return tx_id;
}

inline uint32_t bare_dma_start_1d_reduction(uint64_t dst, uint64_t src, size_t size,
                                            collective_compute_format_t fmt,
                                            uint16_t row_mask, uint16_t col_mask) {
    volatile uint32_t *d = flex_dma_csr();
    flex_dma_program_addr(dst, src, size);
    d[FLEX_DMA_REG_MASK]       = ((uint32_t)col_mask << 16) | (uint32_t)row_mask;
    d[FLEX_DMA_REG_REDUCT_FMT] = (uint32_t)fmt;
    d[FLEX_DMA_REG_MODE]       = FLEX_DMA_MODE_REDUCE;
    __sync_synchronize();
    uint32_t tx_id = d[FLEX_DMA_REG_LAUNCH];
    __sync_synchronize();
    return tx_id;
}

inline void bare_dma_wait_all(void) {
    volatile uint32_t *d = flex_dma_csr();
    while (d[FLEX_DMA_REG_STATUS]) {
        ;
    }
}


/*************************************
*  Basic Asynchronize DMA Interface  *
*************************************/

//Basic DMA 1d transfter
void flex_dma_async_1d(uint64_t dst_addr, uint64_t src_addr, size_t transfer_size){
    bare_dma_start_1d(dst_addr, src_addr, transfer_size);
}

//Basic DMA 2d transfter
void flex_dma_async_2d(uint64_t dst_addr, uint64_t src_addr, size_t transfer_size, size_t dst_stride, size_t src_stride, size_t repeat){
    bare_dma_start_2d(dst_addr, src_addr, transfer_size, dst_stride, src_stride, repeat);
}

//Basic collective primitives
void flex_dma_async_broadcast(uint64_t dst_offset, uint64_t src_offset, size_t transfer_size, uint16_t row_mask, uint16_t col_mask){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d_broadcast(remote_pos(pos,dst_offset), local(src_offset), transfer_size, row_mask, col_mask);
}

void flex_dma_async_reduction(uint64_t dst_offset, uint64_t src_offset, size_t transfer_size, collective_compute_format_t fmt, uint16_t row_mask, uint16_t col_mask){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d_reduction(local(dst_offset), remote_pos(pos,src_offset), transfer_size, fmt, row_mask, col_mask);
}

//wait for idma
void flex_dma_async_wait_all(){
    bare_dma_wait_all();
}

/*************************************
*  Basic Synchronize DMA Interface   *
*************************************/

//Basic DMA 2d transfter
void flex_dma_sync_2d(uint64_t dst_addr, uint64_t src_addr, size_t transfer_size, size_t dst_stride, size_t src_stride, size_t repeat){
    bare_dma_start_2d(dst_addr, src_addr, transfer_size, dst_stride, src_stride, repeat);
    bare_dma_wait_all();
}

/****************************************
*  Versitle Asynchronize DMA Functions  *
****************************************/


void flex_dma_async_Load_HBM_1d(uint32_t local_offset, uint32_t hbm_offset, size_t transfer_size){
    bare_dma_start_1d(local(local_offset),hbm_addr(hbm_offset), transfer_size);
}

//Basic DMA 1d transfter store to HBM
void flex_dma_async_Store_HBM_1d(uint32_t local_offset, uint32_t hbm_offset, size_t transfer_size){
    bare_dma_start_1d(hbm_addr(hbm_offset), local(local_offset), transfer_size);
}

/*******************************************
*  Traffic Pattern: Asynchronize Interface *
*******************************************/

//Pattern: Round Shift Right
void flex_dma_async_pattern_round_shift_right(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_pos(left_pos(pos),remote_offset), transfer_size);
}

//Pattern: Round Shift Left
void flex_dma_async_pattern_round_shift_left(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_pos(right_pos(pos),remote_offset), transfer_size);
}

void flex_dma_async_pattern_round_shift_up(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_pos(bottom_pos(pos),remote_offset), transfer_size);
}


//Pattern All-to-One
void flex_dma_async_pattern_all_to_one(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_xy(0,0,remote_offset), transfer_size);
}

//Pattern Dialog-to-Dialog
void flex_dma_async_pattern_dialog_to_dialog(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_xy(pos.y,pos.x,remote_offset), transfer_size);
}

//Pattern Access West HBM
void flex_dma_async_pattern_access_west_hbm(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),hbm_west(pos.y,remote_offset), transfer_size);
}

//Pattern Access South HBM
void flex_dma_async_pattern_access_south_hbm(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),hbm_south(pos.x,remote_offset), transfer_size);
}

/******************************************
*  Traffic Pattern: Synchronize Interface *
******************************************/

//Pattern: Round Shift Right
void flex_dma_pattern_round_shift_right(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_pos(left_pos(pos),remote_offset), transfer_size);
    bare_dma_wait_all();
}

//Pattern: Round Shift Left
void flex_dma_pattern_round_shift_left(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_pos(right_pos(pos),remote_offset), transfer_size);
    bare_dma_wait_all();
}

void flex_dma_pattern_round_shift_up(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_pos(bottom_pos(pos),remote_offset), transfer_size);
    bare_dma_wait_all();
}


//Pattern All-to-One
void flex_dma_pattern_all_to_one(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_xy(0,0,remote_offset), transfer_size);
    bare_dma_wait_all();
}

//Pattern Dialog-to-Dialog
void flex_dma_pattern_dialog_to_dialog(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),remote_xy(pos.y,pos.x,remote_offset), transfer_size);
    bare_dma_wait_all();
}

//Pattern Access West HBM
void flex_dma_pattern_access_west_hbm(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){
    FlexPosition pos = get_pos(flex_get_cluster_id());
    bare_dma_start_1d(local(local_offset),hbm_west(pos.y,remote_offset), transfer_size);
    bare_dma_wait_all();
}


//Pattern Systolic-like Shifting
void flex_dma_pattern_systolic_shift_west_south(uint32_t local_offset, uint32_t remote_offset, size_t transfer_size){

    FlexPosition pos = get_pos(flex_get_cluster_id());

    if(pos.x == 0){
        /* clusters at west edge hbm transfer*/
        bare_dma_start_1d(local(local_offset),hbm_west(pos.y,remote_offset), transfer_size);
    } else {
        /* clusters on-chip transfer*/
        bare_dma_start_1d(local(local_offset),remote_pos(left_pos(pos),remote_offset), transfer_size);
    }

    if (pos.y == 0)
    {
        /* clusters at south edge hbm transfer*/
        bare_dma_start_1d(local(local_offset),hbm_south(pos.x,remote_offset), transfer_size);
    } else {
        /* clusters on-chip transfer*/
        bare_dma_start_1d(local(local_offset),remote_pos(bottom_pos(pos),remote_offset), transfer_size);
    }

    bare_dma_wait_all();
}

#endif
