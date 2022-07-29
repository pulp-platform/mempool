#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define REPETITIONS 10 /* Number of times to run each test */
#define SLEEPTIME 1000

void work1() {
  int sum = 0;
  for (int i = 0; i < 100; i++) {
    sum++;
  }
}

uint32_t test_omp_parallel_for() {
  uint32_t core_id;
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }
    core_id = mempool_get_core_id();
  }
  return sum;
}

uint32_t test_omp_parallel_for_dynamic() {
  uint32_t core_id;
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }
    core_id = mempool_get_core_id();
  }
  return sum;
}

uint32_t test_omp_parallel_for_dynamic_static() {
  uint32_t core_id;
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }
    core_id = mempool_get_core_id();

    sum = 0;
#pragma omp for schedule(static) reduction(+ : sum)
    for (int i = -100; i <= 0; i++) {
      sum += i;
    }
  }
  return sum;
}

uint32_t test_omp_many() {
  uint32_t core_id;
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }
    core_id = mempool_get_core_id();

#pragma omp barrier

#pragma omp master
    {
      printf("first sum: %d\n", sum);
      sum = 0;
    }

#pragma omp barrier

#pragma omp for schedule(static) reduction(+ : sum)
    for (int i = -10; i <= 0; i++) {
      sum += i;
    }

#pragma omp barrier

#pragma omp single
    { printf("second sum: %d\n", sum); }
  }
  return sum;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t i;

  // mempool_barrier_init(core_id);

  if (core_id == 0) {
    mempool_wait(4 * num_cores);
    printf("Master Thread start\n");
    for (i = 0; i < REPETITIONS; i++) {
      printf("Test: %d\n", i);
      printf("For loop-sum is: %d\n", test_omp_parallel_for());
      printf("For loop dynamic-sum is: %d\n", test_omp_parallel_for_dynamic());
      printf("For loop dynamic-static-sum is: %d\n",
             test_omp_parallel_for_dynamic_static());
      printf("Test many omp-sum is: %d\n", test_omp_many());
      printf("Test finished: %d\n", i);
    }
    printf("Master Thread end\n\n\n");
    mempool_wait(4 * num_cores);
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }
  // mempool_barrier(num_cores);

  return 0;
}
