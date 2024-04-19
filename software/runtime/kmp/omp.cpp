#include "omp.h"
#include "runtime.hpp"

extern "C" {
#include "printf.h"
}

void not_implemented(void) { printf("Not implemented\n"); }

uint32_t omp_get_num_threads(void) {
  return kmp::runtime::getCurrentThread()
      .getCurrentTask()
      ->get()
      .getNumThreads();
}
uint32_t omp_get_thread_num(void) {
  return kmp::runtime::getCurrentThread().getTid();
};
