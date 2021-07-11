#ifndef __OMP_LOCK_H__
#define __OMP_LOCK_H__

#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

typedef uint32_t omp_lock_t;

/* gomp_hal_lock() - block until able to acquire lock "lock" */
static inline void
gomp_hal_lock( omp_lock_t *lock )
{
  uint32_t islocked = 1;

  while(islocked){
    islocked = __atomic_fetch_or(lock, 1, __ATOMIC_SEQ_CST);
  }
}

/* gomp_hal_unlock() - release lock "lock" */
static inline void
gomp_hal_unlock( omp_lock_t *lock )
{
  __atomic_fetch_and(lock, 0, __ATOMIC_SEQ_CST);
}

#endif
