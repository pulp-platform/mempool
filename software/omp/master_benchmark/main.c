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

void parallel_master_manual() {
  uint32_t core_id;
  uint32_t num_cores = mempool_get_core_count();
  core_id = mempool_get_core_id();

  work1();

  mempool_timer_t cycles = mempool_get_timer();
  mempool_start_benchmark();

  if (core_id == 0) {
    result = 100;
  }

  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;

  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("Manual Master Result: %d\n", result);
    printf("Manual Master Duration: %d\n", cycles);
  }
}

void omp_parallel_master() {
  uint32_t num_cores = mempool_get_core_count();

#pragma omp parallel num_threads(num_cores)
  {
    work1();

    mempool_timer_t cycles = mempool_get_timer();
    mempool_start_benchmark();

#pragma omp master
    { result = 100; }

    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;

    mempool_barrier(num_cores);

#pragma omp master
    {
      printf("OMP Master Result: %d\n", result);
      printf("OMP Master Duration: %d\n", cycles);
    }
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // #ifdef VERBOSE
  if (core_id == 0) {
    printf("Initialize\n");
    *checkfirst = 0;
    result = 0;
  }

  mempool_barrier(num_cores);
  parallel_master_manual();
  mempool_barrier(num_cores);

  result = 0;

  /*  OPENMP IMPLEMENTATION  */

  if (core_id == 0) {
    mempool_wait(1 * num_cores);
    omp_parallel_master();
    mempool_wait(4 * num_cores);
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }
  return 0;
}
