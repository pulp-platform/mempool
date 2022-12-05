// Copyright 2021 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Gua Hao Khov, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define DATA_SIZE 32

#define QLR_REG_T0 (5 << 5)
#define QLR_REG_T1 (6 << 5)
#define QLR_REG_T2 (7 << 5)
#define QLR_REG_T3 (28 << 5)
#define QLR_CFG_BASE 0x40010000
#define QLR_CFG_TYPE (QLR_CFG_BASE + (0 << 2))
#define QLR_CFG_REQ (QLR_CFG_BASE + (2 << 2))
#define QLR_CFG_RF (QLR_CFG_BASE + (3 << 2))
#define QLR_CFG_IADDR (QLR_CFG_BASE + (4 << 2))
#define QLR_CFG_OADDR (QLR_CFG_BASE + (5 << 2))

register int32_t qlr_reg asm("t0");

int32_t *qlr_t0_cfg_type = (int32_t *)(QLR_CFG_TYPE + QLR_REG_T0);
int32_t *qlr_t0_cfg_req = (int32_t *)(QLR_CFG_REQ + QLR_REG_T0);
int32_t *qlr_t0_cfg_rf = (int32_t *)(QLR_CFG_RF + QLR_REG_T0);
int32_t *qlr_t0_cfg_iaddr = (int32_t *)(QLR_CFG_IADDR + QLR_REG_T0);
int32_t *qlr_t0_cfg_oaddr = (int32_t *)(QLR_CFG_OADDR + QLR_REG_T0);

int32_t *queues[NUM_CORES];

int32_t data[DATA_SIZE];
int32_t check_array[NUM_CORES];

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  extern int32_t __seq_start;

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id);

  // Setup
  if (core_id == 0) {
    printf("Initialize\n");
    // Fill data array
    for (int32_t i = 0; i < DATA_SIZE; ++i) {
      data[i] = i + 1;
    }
    // Calculate bank addresses of queues
    for (uint32_t i = 0; i < num_cores; ++i) {
      queues[i] = (int32_t *)(sizeof(int32_t) * i);
    }
    // Print out queue addresses
    // printf("queues:\n");
    // for (uint32_t i = 0; i < num_cores; ++i) {
    //   printf("%5d ", queues[i]);
    // }
    // printf("\n");
  }

  // Wait for all cores
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  // Local check
  int32_t check = 0;

  // Front
  if (core_id == 0) {
    // QLR configuration
    *qlr_t0_cfg_req = DATA_SIZE;
    *qlr_t0_cfg_oaddr = (int32_t)queues[1];
    *qlr_t0_cfg_type = 2;
    // Accumulation
    for (uint32_t i = 0; i < DATA_SIZE; ++i) {
      qlr_reg = data[i];
      __asm__ __volatile__("" : "=r"(qlr_reg));
      check += qlr_reg;
    }
  }

  // Mid
  if ((core_id != 0) && (core_id != num_cores - 1)) {
    // QLR configuration
    *qlr_t0_cfg_req = DATA_SIZE;
    *qlr_t0_cfg_rf = 1;
    *qlr_t0_cfg_iaddr = (int32_t)queues[core_id];
    *qlr_t0_cfg_oaddr = (int32_t)queues[core_id + 1];
    *qlr_t0_cfg_type = 3;
    // Accumulation
    for (uint32_t i = 0; i < DATA_SIZE; ++i) {
      check += qlr_reg;
      __asm__ __volatile__("" : "=r"(qlr_reg));
    }
  }

  // End
  if (core_id == num_cores - 1) {
    // QLR configuration
    *qlr_t0_cfg_req = DATA_SIZE;
    *qlr_t0_cfg_rf = 1;
    *qlr_t0_cfg_iaddr = (int32_t)queues[core_id];
    *qlr_t0_cfg_type = 1;
    // Accumulation
    for (uint32_t i = 0; i < DATA_SIZE; ++i) {
      check += qlr_reg;
      __asm__ __volatile__("" : "=r"(qlr_reg));
    }
  }

  // Store check
  check_array[core_id] = check;

  // Wait for all cores
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  // Print check
  if (core_id == 0) {
    printf("Check: %d\n", check_array[0]);
    check = 1;
    for (uint32_t core = 1; core < num_cores; ++core) {
      if (check_array[core] != check_array[0]) {
        check = 0;
        break;
      }
    }
    if (check == 1) {
      printf("Success!\n");
    }
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
