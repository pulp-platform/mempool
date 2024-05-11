#include "barrier.hpp"
#include "kmp/util.hpp"
#include <cassert>
#include <cstdint>

extern "C" {
#include "runtime.h"
}

namespace kmp {
Barrier::Barrier(uint32_t numThreads)
    : barrier(new std::atomic<kmp_uint32>(0)), numThreads(numThreads) {}

void Barrier::wait() const {
  // Increment the barrier counter
  if ((numThreads - 1) == barrier->fetch_add(1, std::memory_order_relaxed)) {
    DEBUG_PRINT("Barrier done\n");
    barrier->store(0, std::memory_order_relaxed);
    std::atomic_thread_fence(std::memory_order_seq_cst);
    wake_up_all();
  } else {
    DEBUG_PRINT("Barrier waiting\n");
  }
  // Some threads have not reached the barrier --> Let's wait
  // Clear the wake-up trigger for the last core reaching the barrier as well
  mempool_wfi();
};

void Barrier::setNumThreads(uint32_t numThreads) {
  assert(*barrier == 0 &&
         "Cannot change the number of threads while the barrier is active");
  this->numThreads = numThreads;
}

Barrier::~Barrier() {
  DEBUG_PRINT("Destroying barrier at %p\n", barrier);
  delete barrier;
}

}; // namespace kmp
