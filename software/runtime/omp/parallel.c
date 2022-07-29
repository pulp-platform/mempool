/* This file handles the (bare) PARALLEL construct.  */

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

event_t event;
work_t works;

void set_event(void (*fn)(void *), void *data, uint32_t nthreads) {
  // int* dd = (int*) data;
  // printf("task %d %d %d %d %d %d \n", *dd, *(dd+1), *(dd+2), *(dd+3),
  // *(dd+4), *(dd+5)); printf("task %d %d %d %d %d %d \n", dd, (dd+1), (dd+2),
  // (dd+3), (dd+4), (dd+5));
  event.fn = fn;
  event.data = data;
  if (nthreads == 0) {
    event.nthreads = NUM_CORES;
    event.barrier = NUM_CORES;
  } else {
    event.nthreads = nthreads;
    event.barrier = nthreads;
  }

  for (uint32_t i = 0; i < NUM_CORES; i++) {
    event.thread_pool[i] = (i < event.nthreads) ? 1 : 0;
  }
}

void run_task(uint32_t core_id) {
  if (event.thread_pool[core_id]) {
    // printf("r\n");
    event.fn(event.data);
    // printf("t\n");
    __atomic_add_fetch(&event.barrier, -1, __ATOMIC_SEQ_CST);
  }
}

void GOMP_parallel_start(void (*fn)(void *), void *data,
                         unsigned int num_threads) {
  // printf("GOMP_parallel_start\n");
  set_event(fn, data, num_threads);
  wake_up((uint32_t)-1);
}

void GOMP_parallel_end(void) {
  // printf("GOMP_parallel_end\n");
  while (event.barrier > 0) {
    mempool_wait(4 * NUM_CORES);
  }
}

void GOMP_parallel(void (*fn)(void *), void *data, unsigned int num_threads,
                   unsigned int flags) {
  // printf("GOMP_parallel\n");
  uint32_t core_id = mempool_get_core_id();

  gomp_new_work_share();

  GOMP_parallel_start(fn, data, num_threads);
  run_task(core_id);
  GOMP_parallel_end();
}

/* The public OpenMP API for thread and team related inquiries.  */

uint32_t omp_get_num_threads(void) {
  // printf("a\n");
  return event.nthreads;
}

uint32_t omp_get_thread_num(void) {
  // printf("b\n");
  return mempool_get_core_id();
}
