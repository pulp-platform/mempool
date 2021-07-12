/* This file handles the BARRIER construct. */

#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

extern uint32_t volatile barrier;
extern uint32_t volatile barrier_iteration;
extern uint32_t volatile barrier_init;
uint32_t volatile barrier_init_gomp __attribute__((section(".l2"))) = 0;

void mempool_barrier_gomp(uint32_t core_id, uint32_t num_cores) {
  if (barrier_init_gomp == 0){
    if (core_id == 0) {
      barrier = 0;
      barrier_iteration = 0;
      barrier_init = 1;
      barrier_init_gomp = 1;
    } else {
      while (!barrier_init)
	mempool_wait(2 * num_cores);
    }
  }
  // Remember previous iteration
  uint32_t iteration_old = barrier_iteration;

  // Increment the barrier counter
  if ((num_cores - 1) == __atomic_fetch_add(&barrier, 1, __ATOMIC_SEQ_CST)) {
    barrier = 0;
    __atomic_fetch_add(&barrier_iteration, 1, __ATOMIC_SEQ_CST);
  } else {
    // Some threads have not reached the barrier --> Let's wait
    while (iteration_old == barrier_iteration)
      mempool_wait(num_cores*2);
  }
}

void GOMP_barrier(){
    // printf("GOMP barrier\n");
    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = event.nthreads;
    mempool_barrier_gomp(core_id, num_cores);
}

