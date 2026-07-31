#ifndef _MC_DUMP_H_
#define _MC_DUMP_H_

#include "mc_runtime.h"
#include "mc_dma_pattern.h"
#include <stddef.h>

/************************
*      Dumping Data     *
************************/

void mc_dump_open(){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE);
    *dump_reg = mc_get_enable_value();
}

void mc_dump_stamp(){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 4);
    *dump_reg = mc_get_enable_value();
}

void mc_dump_close(){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 8);
    *dump_reg = mc_get_enable_value();
}

void mc_dump_set_lower_base(uint32_t val){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 12);
    *dump_reg = val;
}

void mc_dump_set_upper_base(uint32_t val){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 16);
    *dump_reg = val;
}

void mc_dump_set_base(uint64_t val){
    uint32_t lower = (uint32_t) (val >> 0);
    uint32_t upper = (uint32_t) (val >> 32);
    mc_dump_set_lower_base(lower);
    mc_dump_set_upper_base(upper);
    mc_dump_stamp();
}

void mc_dump_hbm(uint64_t hbm_offset, size_t size){
	mc_dump_set_base(hbm_offset);
	mc_dma_async_1d((ARCH_CLUSTER_TCDM_BASE+ARCH_CLUSTER_TCDM_SIZE), hbm_addr(hbm_offset), size);
	mc_dma_async_wait_all();
}


#endif
