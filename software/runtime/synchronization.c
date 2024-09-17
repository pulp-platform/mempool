// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdbool.h>
#include <stdint.h>

#include "runtime.h"
#include "synchronization.h"

uint32_t volatile barrier __attribute__((section(".l1")));
uint32_t volatile log_barrier[NUM_CORES * BANKING_FACTOR]
    __attribute__((aligned(NUM_CORES * BANKING_FACTOR), section(".l1")));
uint32_t volatile partial_barrier[NUM_CORES * BANKING_FACTOR]
    __attribute__((aligned(NUM_CORES * BANKING_FACTOR), section(".l1")));

void mempool_barrier_init(uint32_t core_id) {
  if (core_id == 0) {
    // Initialize the barrier
    barrier = 0;
    set_wake_up_stride(1U);
    set_wake_up_offset(0U);
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

/**
  @brief         Central counter barrier
  @param[in]     num_cores
  @return        none
*/
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

/**
  @brief         Central counter barrier with stride and offset
  @param[in]     num_cores
  @param[in]     stride Stride between cores to wake up
  @param[in]     offset ID of the first core involved in the barrier
  @return        none
*/
void mempool_strided_barrier(uint32_t num_cores, uint32_t stride,
                             uint32_t offset) {
  // Increment the barrier counter
  if (num_cores - offset - stride ==
      __atomic_fetch_add(&log_barrier[stride], stride, __ATOMIC_RELAXED)) {
    __atomic_store_n(&log_barrier[stride], 0, __ATOMIC_RELAXED);
    set_wake_up_stride(stride);
    set_wake_up_offset(offset);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
    set_wake_up_stride(1U);
    set_wake_up_offset(0U);
  }
  mempool_wfi();
}

/* LOG BARRIER */

/**
  @brief         Central counter on cc_cores + log2 tree barrier
  @param[in]     num_cc_cores Number of cores in central counter barrier
  @param[in]     core_id ID of the core arriving at the barrier
  @return        none
*/
void mempool_log2_barrier(uint32_t num_cc_cores, uint32_t core_id) {

  uint32_t num_synch = num_cc_cores;
  uint32_t step = num_cc_cores;
  uint32_t previous_step = 1U;
  uint32_t idx;

  while (step <= NUM_CORES) {
    idx = (step * (core_id / step) * BANKING_FACTOR);
    idx += previous_step - 1; // Avoids overlapping writes
    if (num_synch - 1 ==
        __atomic_fetch_add(&log_barrier[idx], 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&log_barrier[idx], 0, __ATOMIC_RELAXED);
      if (step == NUM_CORES) {
        // Last core wakes-up everyone
        __sync_synchronize();
        wake_up_all();
      }
      // Update values for next iteration
      previous_step = step;
      step <<= 1;
      num_synch = 2;
    } else {
      break;
    }
  }
  mempool_wfi();
}

/**
  @brief         Log2 tree barrier with stride and offset
  @param[in]     num_cc_cores Number of cores in central counter barrier
  @param[in]     core_id ID of the core arriving at the barrier
  @param[in]     stride Stride between cores to wake up
  @param[in]     offset ID of the first core involved in the barrier
  @return        none
*/
void mempool_strided_log2_barrier(uint32_t num_cc_cores, uint32_t core_id,
                                  uint32_t stride, uint32_t offset) {

  // N.B This can incur locks if other cores are running strided barrier
  // N.B Offset can only be 1/2, 3/4, 7/8 cluster otherwise binary tree is not
  // complete

  uint32_t num_synch = num_cc_cores;
  uint32_t step = num_cc_cores * stride;
  uint32_t previous_step = num_cc_cores;
  uint32_t idx;

  uint32_t num_cores = NUM_CORES - offset;

  while (step <= num_cores) {
    idx = (step * (core_id / step) * BANKING_FACTOR);
    idx += previous_step - 1; // Avoids overlapping writes
    if (num_synch - 1 ==
        __atomic_fetch_add(&log_barrier[idx], 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&log_barrier[idx], 0, __ATOMIC_RELAXED);
      if (step == num_cores) {
        // Last core wakes-up everyone
        set_wake_up_stride(stride);
        set_wake_up_offset(offset);
        __sync_synchronize();
        wake_up_all();
        set_wake_up_stride(1U);
        set_wake_up_offset(0U);
      }
      // Update values for next iteration
      previous_step = step;
      step <<= 1;
      num_synch = 2;
    } else {
      break;
    }
  }
  mempool_wfi();
}

/**
  @brief         LogR tree barrier. In each step, central counter.
  @param[in]     num_cc_cores Number of cores in central counter barrier
  @param[in]     core_id ID of the core arriving at the barrier
  @param[in]     radix barrier radix
  @return        none
*/
void mempool_logR_barrier(uint32_t num_cc_cores, uint32_t core_id,
                          uint32_t radix) {

  uint32_t num_synch = num_cc_cores;
  uint32_t step = num_cc_cores;
  uint32_t previous_step = 1U;
  uint32_t idx;

  while (step <= NUM_CORES) {
    idx = (step * (core_id / step) * BANKING_FACTOR);
    idx += previous_step - 1; // Avoids overlapping writes
    if (num_synch - 1 ==
        __atomic_fetch_add(&log_barrier[idx], 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&log_barrier[idx], 0, __ATOMIC_RELAXED);
      if (step == NUM_CORES) {
        // Last core wakes-up everyone
        __sync_synchronize();
        wake_up_all();
      }
      // Update values for next iteration
      previous_step = step;
      step *= radix;
      num_synch = radix;
    } else {
      break;
    }
  }
  mempool_wfi();
}

/* PARTIAL BARRIER */

/**
  @brief         Log2 tree barrier on a subset of cores
  @param[in]     step Step of the logarithmic tree (must be set to 2)
  @param[in]     core_id ID of the first core involved in the barrier
  @param[in]     num_cores_barrier Number of cores involved in the barrier
  @return        none
*/
void mempool_log_partial_barrier(uint32_t step, uint32_t core_id,
                                 uint32_t num_cores_barrier) {

  uint32_t core_init = num_cores_barrier * (core_id / num_cores_barrier);
  uint32_t core_end = core_init + num_cores_barrier;
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
        if (num_cores_barrier >= NUM_CORES) {
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

/**
  @brief         Central counter barrier on a subset of cores
  @param[in]     core_id  ID of the first core involved in the barrier
  @param[in]     core_init First core involved in the barrier
  @param[in]     num_sleeping_cores Number of cores involved in the barrier
  @param[in]     memloc Location of the barrier variable
  @return        none
*/
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
