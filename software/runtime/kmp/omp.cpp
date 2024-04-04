#include "omp.h"

extern "C" {
#include "runtime.h"
}

void not_implemented(void) {
  printf("Not implemented\n");
}

uint32_t omp_get_num_threads(void) { return mempool_get_core_count(); }
uint32_t omp_get_thread_num(void) { return mempool_get_core_id(); };
