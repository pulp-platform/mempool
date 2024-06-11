// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

  inline void wait() {
    DEBUG_PRINT("Entering barrier at %p\n", this);

    // Increment the barrier counter
    if ((numThreads - 1) == barrier.fetch_add(1, std::memory_order_relaxed)) {
      DEBUG_PRINT("Barrier done at %p\n", this);
      barrier.store(0, std::memory_order_relaxed);
      std::atomic_thread_fence(std::memory_order_seq_cst);
      wake_up_all();
    }

    // Some threads have not reached the barrier --> Let's wait
    // Clear the wake-up trigger for the last core reaching the barrier as well
    mempool_wfi();
    DEBUG_PRINT("Exiting barrier at %p\n", this);
  };

  inline void setNumThreads(uint32_t numThreads) {
    assert(barrier == 0 &&
           "Cannot change the number of threads while the barrier is active");
    this->numThreads = numThreads;
  }

private:
  std::atomic<kmp_uint32> barrier;
  volatile uint32_t numThreads;
};
}; // namespace kmp
