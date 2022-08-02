// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#ifndef __SYNCHRONIZATION_H__
#define __SYNCHRONIZATION_H__

// Barrier functions
void mempool_barrier_init(uint32_t core_id);
void mempool_barrier(uint32_t num_cores);
void mempool_log_barrier(uint32_t step, uint32_t core_id);
void mempool_log_partial_barrier(uint32_t step, uint32_t core_id,
                                 uint32_t num_cores_barrier);
void mempool_partial_barrier(uint32_t volatile core_id,
                             uint32_t volatile core_init,
                             uint32_t volatile num_sleeping_cores,
                             uint32_t volatile memloc);

#endif // __SYNCHRONIZATION_H__
