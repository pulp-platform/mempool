// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Bowen Wang <bowwang@student.ethz.ch>

#include "alloc.h"
#include "alloc_partition.h"
#include "runtime.h"
#include "printf.h"

extern partition_status_t volatile partition_status[NUM_PART_REGION];

// ========================================================================================
// Allocate a region in L1 for a single or several matrices
// @inp: (uint32_t)            size         --- size of the single allocated matrix
// @inp: (uint32_t)            num_matrix   --- How many mtrices in this region
// @inp: (int32_t* volitile *) target       --- Where to store this pointer
// @inp: (uint32_t)            group_factor --- GF_A/B/C
// ========================================================================================
void alloc_matrix (float *volatile * target, uint32_t size, uint32_t group_factor, uint32_t num_matrix){

    // 1. Get allocator for sequential Heap region
    uint32_t total_size = size*num_matrix;
    alloc_t* alloc_heap = get_dynamic_heap_alloc(0);

    // 2. alloc a space, store the return address to the target
    *target = (float *)partition_malloc(alloc_heap, total_size*sizeof(float), total_size/NUM_ELEMENTS_PER_ROW);
    // 3. find which partition in free
    uint32_t pid=0;
    uint32_t avail=0;
    while( (pid<NUM_PART_REGION) && (avail==0)){
        if (partition_status[pid].status==0){
            avail=1;
            partition_status[pid].data_addr = *target;
            partition_status[pid].status    = 1;
            printf("Dynamic Allocator >> pid[%d], start_addr[%p].\n", pid, *target);
        }
        else{
            pid++;
        }
    }
    if ( (pid==NUM_PART_REGION) && (avail==0) ){
        printf("Dynamic Allocator >> WARNING: No available partition region.\n");
    }

    // 4. Config the hardware
    printf("Dynamic Allocator >> pid[%d] parallel_sections[%d] elements_per_section[%d]\n", pid, NUM_TILES/group_factor, size);
    partition_config(pid, group_factor);
    start_addr_scheme_config(pid, (uint32_t)(*target), total_size);

    // 5. Handle multi-matrices
    if (num_matrix > 1){
        for (uint32_t ii=1; ii<num_matrix; ++ii){
            *(target+ii) = *target + ii*size;
        }
    }
}


void free_matrix(float *__restrict__ heap_matrix, uint32_t part_id, uint32_t core_id){
    if (core_id == 0){
        // get allocator for the selected partition
        alloc_t *dynamic_heap_alloc = get_dynamic_heap_alloc(part_id);
        partition_free(dynamic_heap_alloc, heap_matrix);
        // free the partition info
        uint32_t pid=0;
        while(pid<NUM_PART_REGION){
            if (partition_status[pid].data_addr==heap_matrix){
                partition_status[pid].status = 0;
                printf("Dynamic Allocator >> pid[%d] is freed.\n", pid);
                pid++;
            }
            else{
                pid++;
            }
        }
    }
}


void free_alloc(uint32_t core_id){
	if (core_id == 0){
        free_dynamic_heap_alloc();
	}
}