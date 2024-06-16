// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "kmp/omp.h"
#include "kmp/types.h"
#include "kmp/util.hpp"

#include <atomic>
#include <cassert>
#include <cstdint>

extern "C" {
#include "runtime.h"
}

namespace kmp {

namespace runtime {
extern kmp_int32 numTeams;
}

class Barrier {
public:
  Barrier(Barrier &&) = delete;
  Barrier &operator=(Barrier &&) = delete;
  Barrier(kmp_int32 numThreads);
  Barrier(const Barrier &) = delete;
  Barrier &operator=(const Barrier &) = delete;

  ~Barrier();

  inline void wait() {
    if (runtime::numTeams > 0) {
      DEBUG_PRINT("Entering spin barrier at %p\n", this);
      // Spin generation barrier

      kmp_int32 gen = generation;

      // Increment the barrier counter
      if ((numThreads - 1) == barrier.fetch_add(1, std::memory_order_relaxed)) {
        DEBUG_PRINT("Barrier done at %p\n", this);
        barrier.store(0, std::memory_order_relaxed);
        generation.fetch_add(1, std::memory_order_relaxed);
        std::atomic_thread_fence(std::memory_order_seq_cst);
      }

      while (gen == generation.load(std::memory_order_relaxed)) {
        // Spin
      }

    } else {
      DEBUG_PRINT("Entering wfi barrier at %p\n", this);
      // WFI barrier

      // Increment the barrier counter
      if ((numThreads - 1) == barrier.fetch_add(1, std::memory_order_relaxed)) {
        DEBUG_PRINT("Barrier done at %p\n", this);
        barrier.store(0, std::memory_order_relaxed);
        std::atomic_thread_fence(std::memory_order_seq_cst);
        wake_up_all();
      }

      // Some threads have not reached the barrier --> Let's wait
      // Clear the wake-up trigger for the last core reaching the barrier as
      // well
      mempool_wfi();
    }

    DEBUG_PRINT("Exiting barrier at %p\n", this);
  };

  inline void setNumThreads(int32_t numThreads) {
    if (barrier != 0) {
      DEBUG_PRINT("Cannot change the number of threads while the barrier is "
                  "active: %p, %d\n",
                  this, barrier.load());
    }
    assert(barrier == 0 &&
           "Cannot change the number of threads while the barrier is active");

    this->numThreads = numThreads;
  }

private:
  std::atomic<kmp_int32> barrier;
  std::atomic<kmp_int32> generation;
  volatile int32_t numThreads;
};
}; // namespace kmp
