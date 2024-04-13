#include "barrier.hpp"
#include <stdint.h>

extern "C" {
#include "runtime.h"
#include "alloc.h"
}

namespace kmp {
Barrier::Barrier(uint32_t root, uint32_t numCores)
    : root(root), numCores(numCores) {
  barrier = static_cast<uint32_t *>(simple_malloc(sizeof(uint32_t)));
}

void Barrier::wait() {
  // Increment the barrier counter
  if ((numCores - 1) == __atomic_fetch_add(barrier, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(barrier, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
  }
  // Some threads have not reached the barrier --> Let's wait
  // Clear the wake-up trigger for the last core reaching the barrier as well
  mempool_wfi();
};

void Barrier::reset() {
  auto coreId = mempool_get_core_id();
  if (coreId == root) {
    // Initialize the barrier
    barrier = 0;
    wake_up_all();
    mempool_wfi();
  } else {
    mempool_wfi();
  }
}

Barrier::~Barrier() { simple_free(static_cast<void *>(barrier)); }

}; // namespace kmp
