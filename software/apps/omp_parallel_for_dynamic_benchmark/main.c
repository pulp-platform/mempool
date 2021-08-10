#include <stdint.h>
#include <string.h>

#include "data.h"
#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

void spmv(int *y, int *data, int *colidx, int *rowb, int *rowe, int *x, int n) {
  int i, j;
  int sum;
  int rowstart;
  int rowend;
  for (i = 0; i < n; i++) {
    sum = 0;
    rowstart = rowb[i];
    rowend = rowe[i];
    for (j = rowstart; j < rowend; j++) {
      sum += data[j] * x[colidx[j]];
    }
    y[i] = sum;
  }
}

void spmv_static(int *y, int *data, int *colidx, int *rowb, int *rowe, int *x,
                 int n) {
  int i, j;
  int sum;
  int rowstart;
  int rowend;
#pragma omp parallel for num_threads(16)
  for (i = 0; i < n; i++) {
    sum = 0;
    rowstart = rowb[i];
    rowend = rowe[i];
    for (j = rowstart; j < rowend; j++) {
      sum += data[j] * x[colidx[j]];
    }
    y[i] = sum;
  }
}

void spmv_dynamic(int *y, int *data, int *colidx, int *rowb, int *rowe, int *x,
                  int n) {
  int i, j;
  int sum;
  int rowstart;
  int rowend;
#pragma omp parallel for num_threads(16) schedule(dynamic, 4)
  for (i = 0; i < n; i++) {
    sum = 0;
    rowstart = rowb[i];
    rowend = rowe[i];
    for (j = rowstart; j < rowend; j++) {
      sum += data[j] * x[colidx[j]];
    }
    y[i] = sum;
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {

    mempool_wait(1000);

    mempool_timer_t cycles;
    int n = 512;

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    spmv(y, nnz, col, rowb, rowe, x, n);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;
    printf("Sequqntial Duration: %d\n", cycles);

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    spmv_static(y, nnz, col, rowb, rowe, x, n);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;
    printf("Static Duration: %d\n", cycles);

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    spmv_dynamic(y, nnz, col, rowb, rowe, x, n);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;
    printf("Dynamic Duration: %d\n", cycles);

  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
