#include "barrier.hpp"
#include <cassert>
#include <stdint.h>

extern "C" {
#include "alloc.h"
#include "runtime.h"
}

namespace kmp {
Barrier::Barrier(uint32_t numCores) : numCores(numCores) {
  barrier = new std::atomic<kmp_uint32>(0);
}

void Barrier::wait() const {
  // Increment the barrier counter
  if ((numCores - 1) == barrier->fetch_add(1, std::memory_order_relaxed)) {
    barrier->store(0, std::memory_order_relaxed);
    std::atomic_thread_fence(std::memory_order_seq_cst);
    wake_up_all();
  }
  // Some threads have not reached the barrier --> Let's wait
  // Clear the wake-up trigger for the last core reaching the barrier as well
  mempool_wfi();
};

Barrier::~Barrier() {
  delete barrier;
}

}; // namespace kmp
