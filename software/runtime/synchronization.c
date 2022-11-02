// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdbool.h>
#include <stdint.h>

#include "runtime.h"
#include "synchronization.h"

uint32_t volatile barrier __attribute__((section(".l1")));
uint32_t volatile log_barrier[NUM_CORES * 4]
    __attribute__((aligned(NUM_CORES * 4), section(".l1")));
uint32_t volatile partial_barrier[NUM_CORES * 4]
    __attribute__((aligned(NUM_CORES * 4), section(".l1")));

void mempool_barrier_init(uint32_t core_id) {
  if (core_id == 0) {
    // Initialize the barrier
    barrier = 0;
    wake_up_all();
    mempool_wfi();
  } else {
    mempool_wfi();
  }
  // Initialize log-barriers synch variables in parallel
  for (uint32_t i = core_id; i < NUM_CORES * 4; i += NUM_CORES) {
    log_barrier[i] = 0;
    partial_barrier[i] = 0;
  }
  mempool_barrier(NUM_CORES);
}

/* PLAIN BARRIER */

void mempool_barrier(uint32_t num_cores) {
  // Increment the barrier counter
  if ((num_cores - 1) == __atomic_fetch_add(&barrier, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(&barrier, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
  }
  // Some threads have not reached the barrier --> Let's wait
  // Clear the wake-up trigger for the last core reaching the barrier as well
  mempool_wfi();
}

void mempool_strided_barrier(uint32_t *barrier, uint32_t num_cores,
                             uint32_t stride, uint32_t offset) {

  // Increment the barrier counter
  if ((num_cores - 1) == __atomic_fetch_add(barrier, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(barrier, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    set_wake_up_stride(stride);
    set_wake_up_offset(offset);
    wake_up_all();
    set_wake_up_stride(1U);
    set_wake_up_offset(0U);
  }
  mempool_wfi();
}

/* LOG BARRIER */

void mempool_log_barrier(uint32_t step, uint32_t core_id) {

  uint32_t idx = (step * (core_id / step)) * 4;
  uint32_t next_step, previous_step;
  uint32_t num_cores = mempool_get_core_count();

  previous_step = step >> 1;
  if ((step - previous_step) ==
      __atomic_fetch_add(&log_barrier[idx + previous_step - 1], previous_step,
                         __ATOMIC_RELAXED)) {
    next_step = step << 1;
    __atomic_store_n(&log_barrier[idx + previous_step - 1], 0,
                     __ATOMIC_RELAXED);
    if (num_cores == step) {
      __sync_synchronize(); // Full memory barrier
      wake_up_all();
      mempool_wfi();
    } else {
      mempool_log_barrier(next_step, core_id);
    }
  } else
    mempool_wfi();
}

void mempool_strided_log_barrier(uint32_t step, uint32_t core_id,
                                 uint32_t stride, uint32_t offset) {

  uint32_t idx = (step * (core_id / step)) * 4 + offset;
  uint32_t next_step, previous_step;
  uint32_t num_cores = mempool_get_core_count();

  previous_step = step >> 1;
  if ((step - previous_step) ==
      __atomic_fetch_add(&log_barrier[idx + previous_step - 1], previous_step,
                         __ATOMIC_RELAXED)) {
    next_step = step << 1;
    __atomic_store_n(&log_barrier[idx + previous_step - 1], 0,
                     __ATOMIC_RELAXED);
    if (num_cores == step) {
      __sync_synchronize(); // Full memory barrier
      set_wake_up_stride(stride);
      set_wake_up_offset(offset);
      wake_up_all();
      set_wake_up_stride(1U);
      set_wake_up_offset(0U);
      mempool_wfi();
    } else {
      mempool_log_barrier(next_step, core_id);
    }
  } else
    mempool_wfi();
}

/* PARTIAL BARRIER */

void mempool_log_partial_barrier(uint32_t step, uint32_t core_id,
                                 uint32_t num_cores_barrier) {

  uint32_t core_init = num_cores_barrier * (core_id / num_cores_barrier);
  uint32_t core_end = core_init + num_cores_barrier;
  uint32_t num_cores = mempool_get_core_count();
  uint32_t num_cores_per_tile = mempool_get_core_count_per_tile();
  uint32_t num_cores_per_group = mempool_get_core_count_per_group();

  if (core_id >= core_init && core_id < core_end) {

    uint32_t idx = (step * (core_id / step)) * 4;
    uint32_t next_step, previous_step;
    previous_step = step >> 1;
    if ((step - previous_step) ==
        __atomic_fetch_add(&log_barrier[idx + previous_step - 1], previous_step,
                           __ATOMIC_RELAXED)) {
      next_step = step << 1;
      __atomic_store_n(&log_barrier[idx + previous_step - 1], 0,
                       __ATOMIC_RELAXED);
      if (num_cores_barrier == step) {

        __sync_synchronize(); // Full memory barrier
        if (num_cores_barrier >= num_cores) {
          wake_up_all();
        } else if (num_cores_barrier >= num_cores_per_group) {
          uint32_t volatile group_init = core_init / num_cores_per_group;
          uint32_t volatile group_end = core_end / num_cores_per_group;
          wake_up_group(((1U << (group_end - group_init)) - 1) << group_init);
        } else if (num_cores_barrier >= num_cores_per_tile) {
          uint32_t volatile tile_init = core_init / num_cores_per_tile;
          uint32_t volatile tile_end = core_end / num_cores_per_tile;
          wake_up_tile(tile_init / NUM_TILES_PER_GROUP,
                       ((1U << (tile_end - tile_init)) - 1)
                           << tile_init % NUM_TILES_PER_GROUP);
        } else {
          while (core_init < core_end) {
            wake_up(core_init);
            core_init++;
          }
        }
        mempool_wfi();
      } else {
        mempool_log_partial_barrier(next_step, core_id, num_cores_barrier);
      }
    } else
      mempool_wfi();
  }
}

void mempool_partial_barrier(uint32_t volatile core_id,
                             uint32_t volatile core_init,
                             uint32_t volatile num_sleeping_cores,
                             uint32_t volatile memloc) {

  uint32_t volatile core_end = core_init + num_sleeping_cores;
  uint32_t num_cores_per_tile = mempool_get_core_count_per_tile();
  uint32_t num_cores_per_group = mempool_get_core_count_per_group();

  if (core_id >= core_init && core_id < core_end) {

    if (num_sleeping_cores - 1 ==
        __atomic_fetch_add(&partial_barrier[(core_init * 4) + memloc], 1,
                           __ATOMIC_RELAXED)) {

      __atomic_store_n(&partial_barrier[(core_init * 4) + memloc], 0,
                       __ATOMIC_RELAXED);
      __sync_synchronize(); // Full memory barrier
      /* Wake-up the core remainder */
      if ((core_end - core_init) > num_cores_per_tile) {
        while (core_init % num_cores_per_tile != 0) {
          wake_up(core_init);
          core_init++;
        }
        while (core_end % num_cores_per_tile != 0) {
          core_end--;
          wake_up(core_end);
        }
      } else if ((core_end - core_init) < num_cores_per_tile) {
        while (core_init < core_end) {
          wake_up(core_init);
          core_init++;
        }
      }

      /* Wake-up the tile remainder */
      uint32_t volatile tile_init = core_init / num_cores_per_tile;
      uint32_t volatile tile_end = core_end / num_cores_per_tile;
      if ((tile_end - tile_init) > NUM_TILES_PER_GROUP) {
        wake_up_tile(tile_init / NUM_TILES_PER_GROUP,
                     ((1U << (16 - tile_init % NUM_TILES_PER_GROUP)) - 1)
                         << tile_init % NUM_TILES_PER_GROUP);
        wake_up_tile(tile_end / NUM_TILES_PER_GROUP,
                     ((1U << tile_end % NUM_TILES_PER_GROUP) - 1));
        core_init += num_cores_per_tile * (16 - tile_init);
        core_end -= num_cores_per_tile * tile_end % NUM_TILES_PER_GROUP;
      } else if ((tile_end - tile_init) < NUM_TILES_PER_GROUP) {
        wake_up_tile(tile_init / NUM_TILES_PER_GROUP,
                     ((1U << (tile_end - tile_init)) - 1)
                         << tile_init % NUM_TILES_PER_GROUP);
        core_init += num_cores_per_tile * (tile_end - tile_init);
      }

      /* Wake-up the group remainder */
      uint32_t volatile group_init = core_init / num_cores_per_group;
      uint32_t volatile group_end = core_end / num_cores_per_group;
      if (group_end - group_init > 0) {
        wake_up_group(((1U << (group_end - group_init)) - 1) << group_init);
        core_init += num_cores_per_group * (group_end - group_init);
      }
    }
    mempool_wfi();
  }
}
