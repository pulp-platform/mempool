#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

uint32_t *checkfirst;
uint32_t result;
extern uint32_t barrier_init;

void work1() {
  int sum = 0;
  for (int i = 0; i < 100; i++) {
    sum++;
  }
}

parallel_single_manual() {
  uint32_t core_id;
  uint32_t num_cores = mempool_get_core_count();
  core_id = mempool_get_core_id();

  work1();

  mempool_timer_t cycles = mempool_get_timer();
  mempool_start_benchmark();

  if (!__atomic_fetch_or(checkfirst, 1, __ATOMIC_SEQ_CST)) {
    result = 100;
  }

  mempool_barrier(num_cores, num_cores);
  *checkfirst = 0;

  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;

  if (core_id == 0) {
    printf("Manual Single Result: %d\n", result);
    printf("Manual Single Duration: %d\n", cycles);
  }
}

omp_parallel_single() {
  uint32_t core_id;

#pragma omp parallel
  {
    work1();

    mempool_timer_t cycles = mempool_get_timer();
    mempool_start_benchmark();

#pragma omp single
    { result = 100; }

    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;

#pragma omp master
    {
      printf("OMP Single Result: %d\n", result);
      printf("OMP Single Duration: %d\n", cycles);
    }
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id, num_cores);

  // #ifdef VERBOSE
  if (core_id == 0) {
    printf("Initialize\n");
    *checkfirst = 0;
    result = 0;
  }

  mempool_barrier(num_cores, num_cores * 4);

  parallel_single_manual();

  mempool_barrier(num_cores, num_cores * 4);

  barrier_init = 0;
  result = 0;

  /*  OPENMP IMPLEMENTATION  */
  int32_t omp_result;

  if (core_id == 0) {

    omp_parallel_single();

    mempool_wait(4 * num_cores);
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }
  return 0;
}
