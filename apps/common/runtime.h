// Copyright 2020 ETH Zurich and University of Bologna.
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

// Author: Samuel Riedel, ETH Zurich
//         Matheus Cavalcante, ETH Zurich

#pragma once
#include "encoding.h"
#include <stddef.h>
#include <stdint.h>

extern char l1_alloc_base;
extern uint32_t atomic_barrier;
extern uint32_t wake_up_reg;

typedef uint32_t mempool_id_t;
typedef uint32_t mempool_timer_t;

/// Obtain the number of cores in the current cluster.
static inline mempool_id_t mempool_get_core_count() {
  extern uint32_t nr_cores_address_reg;
  return nr_cores_address_reg;
}

/// Obtain the ID of the current core.
static inline mempool_id_t mempool_get_core_id() {
  mempool_id_t r;
  asm volatile("csrr %0, mhartid" : "=r"(r));
  return r;
}

/// Reset a monotonically increasing cycle count.
static inline void mempool_start_benchmark() {
  asm volatile("" ::: "memory");
  write_csr(cycle, 0);
  asm volatile("" ::: "memory");
}

/// Obtain a monotonically increasing cycle count.
static inline uint32_t mempool_stop_benchmark() {
  asm volatile("" ::: "memory");
  return read_csr(cycle);
  asm volatile("" ::: "memory");
}

/// Obtain a monotonically increasing cycle count.
static inline mempool_timer_t mempool_get_timer() { return read_csr(mcycle); }

/// Busy loop for waiting
static inline void mempool_wait(uint32_t cycles) {
  asm volatile("1: \n\t"
               "addi %[counter], %[counter], -2 \n\t"
               "bgtz %[counter], 1b \n\t"
               : [ counter ] "+&r"(cycles)
               :
               : "memory");
}

static inline void mempool_wfi(){
  asm("wfi");
}

static inline void write_wake_up_reg(uint32_t value){
  wake_up_reg = value;
}
