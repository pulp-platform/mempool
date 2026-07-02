#ifndef _FLEX_DUMP_H_
#define _FLEX_DUMP_H_

#include "flex_runtime.h"
#include "flex_dma_pattern.h"
#include <stddef.h>

/************************
*      Dumping Data     *
************************/

void flex_dump_open(){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE);
    *dump_reg = flex_get_enable_value();
}

void flex_dump_stamp(){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 4);
    *dump_reg = flex_get_enable_value();
}

void flex_dump_close(){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 8);
    *dump_reg = flex_get_enable_value();
}

void flex_dump_set_lower_base(uint32_t val){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 12);
    *dump_reg = val;
}

void flex_dump_set_upper_base(uint32_t val){
    volatile uint32_t * dump_reg = (volatile uint32_t *) (ARCH_CLUSTER_REG_BASE + ARCH_CLUSTER_REG_SIZE + 16);
    *dump_reg = val;
}

void flex_dump_set_base(uint64_t val){
    uint32_t lower = val >> 0;
    uint32_t upper = val >> 32;
    flex_dump_set_lower_base(lower);
    flex_dump_set_upper_base(upper);
    flex_dump_stamp();
}

void flex_dump_hbm(uint64_t hbm_offset, size_t size){
	flex_dump_set_base(hbm_offset);
	flex_dma_async_1d((ARCH_CLUSTER_TCDM_BASE+ARCH_CLUSTER_TCDM_SIZE), hbm_addr(hbm_offset), size);
	flex_dma_async_wait_all();
}


#endif