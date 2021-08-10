#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define N 16
#define M 4

void work2(unsigned long num) {
  unsigned int i;
  volatile int cnt = 0;

  for (i = 0; i < num; i++)
    cnt += i;
}

void sequential() {
  for (int i = 0; i < N; i++) {
    work2(100);
  }
}

void static_parallel() {
#pragma omp parallel for num_threads(4)
  for (int i = 0; i < N; i++) {
    work2(100);
  }
}

void dynamic_parallel() {
#pragma omp parallel for num_threads(4) schedule(dynamic, M)
  for (int i = 0; i < N; i++) {
    work2(100);
  }
}

void section_parallel() {
#pragma omp parallel num_threads(4)
  {
#pragma omp sections
    {
#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }

#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }

#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }

#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }
    }
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_timer_t cycles;

  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {

    mempool_wait(10000);

    printf("Sequential Start\n");
    // cycles = mempool_get_timer();
    // mempool_start_benchmark();
    sequential();
    // mempool_stop_benchmark();
    // cycles = mempool_get_timer() - cycles;
    // printf("Sequential Duration: %d\n", cycles);

    printf("Static Start\n");
    // cycles = mempool_get_timer();
    // mempool_start_benchmark();
    static_parallel();
    // mempool_stop_benchmark();
    // cycles = mempool_get_timer() - cycles;
    // printf("Static Duration: %d\n", cycles);

    printf("Dynamic Start\n");
    // cycles = mempool_get_timer();
    // mempool_start_benchmark();
    dynamic_parallel();
    // mempool_stop_benchmark();
    // cycles = mempool_get_timer() - cycles;
    // printf("Dynamic Duration: %d\n", cycles);

    printf("Section Start\n");
    // cycles = mempool_get_timer();
    // mempool_start_benchmark();
    section_parallel();
    // mempool_stop_benchmark();
    // cycles = mempool_get_timer() - cycles;
    // printf("Section Duration: %d\n", cycles);

  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
