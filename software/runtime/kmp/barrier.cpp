#include "barrier.hpp"
#include <stdint.h>

extern "C" {
#include "alloc.h"
#include "runtime.h"
}

namespace kmp {
Barrier::Barrier(uint32_t numCores) : numCores(numCores) {
  barrier = static_cast<volatile uint32_t *>(simple_malloc(sizeof(uint32_t)));
}

void Barrier::wait() {
  // Increment the barrier counter
  if ((numCores - 1) == __atomic_fetch_add(barrier, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(barrier, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    printf("Barrier done\n");
    wake_up_all();
  }
  // Some threads have not reached the barrier --> Let's wait
  // Clear the wake-up trigger for the last core reaching the barrier as well
  mempool_wfi();
};

Barrier::~Barrier() {
  simple_free(const_cast<void *>(static_cast<volatile void *>(barrier)));
}

}; // namespace kmp
