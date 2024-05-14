#pragma once

#include "kmp/types.h"
#include "kmp/util.hpp"
#include <atomic>
#include <cassert>
#include <cstdint>

extern "C" {
#include "runtime.h"
}

namespace kmp {
class Barrier {
public:
  Barrier(Barrier &&) = delete;
  Barrier &operator=(Barrier &&) = delete;
  Barrier(uint32_t numThreads);
  Barrier(const Barrier &) = delete;
  Barrier &operator=(const Barrier &) = delete;

  ~Barrier();

  inline void wait() const {
    DEBUG_PRINT("Entering barrier\n");

    // Increment the barrier counter
    if ((numThreads - 1) == barrier->fetch_add(1, std::memory_order_relaxed)) {
      DEBUG_PRINT("Barrier done\n");
      barrier->store(0, std::memory_order_relaxed);
      std::atomic_thread_fence(std::memory_order_seq_cst);
      wake_up_all();
    }

    // Some threads have not reached the barrier --> Let's wait
    // Clear the wake-up trigger for the last core reaching the barrier as well
    mempool_wfi();
  };

  inline void setNumThreads(uint32_t numThreads) {
    assert(*barrier == 0 &&
           "Cannot change the number of threads while the barrier is active");
    this->numThreads = numThreads;
  }

private:
  std::atomic<kmp_uint32> *barrier;
  uint32_t numThreads;
};
}; // namespace kmp
