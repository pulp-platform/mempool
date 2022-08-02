/* This file handles the BARRIER construct. */

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

extern uint32_t volatile barrier;
extern uint32_t volatile barrier_iteration;
extern uint32_t volatile barrier_init;
uint32_t volatile barrier_init_gomp __attribute__((section(".l2"))) = 0;

void mempool_barrier_gomp(uint32_t core_id, uint32_t num_cores) {
  if (barrier_init_gomp == 0) {
    if (core_id == 0) {
      // Initialize the barrier
      barrier = 0;
      wake_up_all();
      mempool_wfi();
    } else {
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);
}

void GOMP_barrier() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = event.nthreads;
  mempool_barrier_gomp(core_id, num_cores);
}
