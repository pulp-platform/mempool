// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
  write_csr(trace, 1);
  asm volatile("" ::: "memory");
}

/// Obtain a monotonically increasing cycle count.
static inline void mempool_stop_benchmark() {
  asm volatile("" ::: "memory");
  write_csr(trace, 0);
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

static inline void mempool_wfi() { asm volatile("wfi"); }

// Wake up core with given core_id by writing in the wake up control register.
// If core_id equals -1, wake up all cores.
static inline void wake_up(uint32_t core_id) { wake_up_reg = core_id; }
