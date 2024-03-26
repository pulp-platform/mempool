// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef __OMP_LOCK_H__
#define __OMP_LOCK_H__

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

typedef uint32_t omp_lock_t;

/* gomp_hal_lock() - block until able to acquire lock "lock" */
static inline void gomp_hal_lock(omp_lock_t *lock) {
  uint32_t islocked;
  uint32_t num_cores = mempool_get_core_count();

  islocked = __atomic_fetch_or(lock, 1, __ATOMIC_SEQ_CST);
  while (islocked) {
    mempool_wait(num_cores);
    islocked = __atomic_fetch_or(lock, 1, __ATOMIC_SEQ_CST);
  }
}

/* gomp_hal_unlock() - release lock "lock" */
static inline void gomp_hal_unlock(omp_lock_t *lock) {
  __atomic_fetch_and(lock, 0, __ATOMIC_SEQ_CST);
}

#endif
