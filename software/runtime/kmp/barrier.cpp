#include "barrier.hpp"
#include <stdint.h>

extern "C" {
#include "alloc.h"
#include "runtime.h"
}

namespace kmp {
Barrier::Barrier(uint32_t numCores) : numCores(numCores) {
  barrier =
      static_cast<std::atomic<uint32_t> *>(simple_malloc(sizeof(uint32_t)));
  counter = static_cast<std::atomic<uint32_t> *>(
      simple_malloc(sizeof(std::atomic<uint32_t>)));
  *counter = 1;
  *barrier = 0;
}

Barrier::Barrier(const Barrier &other)
    : barrier(other.barrier), counter(other.counter), numCores(other.numCores) {
  (*counter)++;
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
  if (--(*counter) == 0) {
    simple_free(counter);
    simple_free(const_cast<void *>(static_cast<volatile void *>(barrier)));
  }
}

}; // namespace kmp
