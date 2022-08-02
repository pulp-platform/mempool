/* This file handles the LOOP (FOR/DO) construct.  */

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

void gomp_loop_init(int start, int end, int incr, int chunk_size) {
  works.chunk_size = chunk_size;
  works.end = end;
  works.incr = incr;
  works.next = start;
}

/*********************** APIs *****************************/

int GOMP_loop_dynamic_start(int start, int end, int incr, int chunk_size,
                            int *istart, int *iend) {
  int chunk, left;
  int ret = 1;

  if (gomp_work_share_start()) { // work returns locked
    gomp_loop_init(start, end, incr, chunk_size);
  }
  gomp_hal_unlock(&works.lock);

  chunk = chunk_size * incr;

  start = __atomic_fetch_add(&works.next, chunk, __ATOMIC_SEQ_CST);

  if (start >= works.end) {
    ret = 0;
  }

  if (ret) {
    left = works.end - start;

    if (chunk > left) {
      end = works.end;
    } else {
      end = start + chunk;
    }
  }

  *istart = start;
  *iend = end;

  return ret;
}

int GOMP_loop_dynamic_next(int *istart, int *iend) {
  int start, end, chunk, left;

  chunk = works.chunk_size * works.incr;
  start = __atomic_fetch_add(&works.next, chunk, __ATOMIC_SEQ_CST);

  if (start >= works.end) {
    return 0;
  }

  left = works.end - start;

  if (chunk > left) {
    end = works.end;
  } else {
    end = start + chunk;
  }

  *istart = start;
  *iend = end;

  return 1;
}

void GOMP_parallel_loop_dynamic(void (*fn)(void *), void *data,
                                unsigned num_threads, long start, long end,
                                long incr, long chunk_size) {
  uint32_t core_id = mempool_get_core_id();

  gomp_new_work_share();
  gomp_loop_init(start, end, incr, chunk_size);

  GOMP_parallel_start(fn, data, num_threads);
  run_task(core_id);
  GOMP_parallel_end();
}

void GOMP_loop_end() {
  uint32_t core_id = mempool_get_core_id();
  mempool_barrier_gomp(core_id, event.nthreads);
}

void GOMP_loop_end_nowait() {}

int GOMP_loop_ull_dynamic_start(int start, int end, int incr, int chunk_size,
                                int *istart, int *iend) {
  return GOMP_loop_dynamic_start(start, end, incr, chunk_size, istart, iend);
}
int GOMP_loop_ull_dynamic_next(int *istart, int *iend) {
  return GOMP_loop_dynamic_next(istart, iend);
}
