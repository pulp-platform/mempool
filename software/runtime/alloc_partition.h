// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Bowen Wang <bowwang@iis.ethz.ch>

#ifndef _ALLOC_PARTITION_H_
#define _ALLOC_PARTITION_H_

// ============================================================
//                    Dynamic Data Pointers
// ============================================================
#define NUM_TILES (128)
#ifdef FLOAT_APP
float* volatile Region_A[NUM_TILES] __attribute__((section(".l1")));
float* volatile Region_B[NUM_TILES] __attribute__((section(".l1")));
float* volatile Region_C[NUM_TILES] __attribute__((section(".l1")));
float* volatile Region_D[NUM_TILES] __attribute__((section(".l1")));
#endif

#ifdef INT_APP
int32_t* volatile Region_A[NUM_TILES] __attribute__((section(".l1")));
int32_t* volatile Region_B[NUM_TILES] __attribute__((section(".l1")));
int32_t* volatile Region_C[NUM_TILES] __attribute__((section(".l1")));
int32_t* volatile Region_D[NUM_TILES] __attribute__((section(".l1")));
#endif

// ============================================================
//                      Group Factor
// ============================================================
#ifndef _GF
#define _GF
#define GF_TILE    (1)
#define GF_SUBG    (8)
#define GF_GROUP   (32)
#define GF_CLUSTER (128)
#endif

// ============================================================
//               Dynamic Heap Region Status
// ============================================================
#define NUM_ELEMENTS_PER_ROW (4096)
#define NUM_PART_REGION      (4) 
typedef struct {
  float *data_addr;     // trace which matrix belong to this partition
  uint32_t status;        // set to 1 if used
} partition_status_t;

// ============================================================
//                    Helper Functions 
// ============================================================
void alloc_matrix(float *volatile * target, uint32_t size, uint32_t group_factor, uint32_t num_matrix);

void free_matrix(float *__restrict__ heap_matrix, uint32_t part_id, uint32_t core_id);

void free_alloc(uint32_t core_id);

#endif