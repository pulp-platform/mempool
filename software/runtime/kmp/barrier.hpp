#pragma once

#include "kmp/types.h"
#include <atomic>
#include <cstdint>

namespace kmp {
class Barrier {
public:
  Barrier(uint32_t numThreads);
  Barrier(const Barrier &) = delete;
  Barrier &operator=(const Barrier &) = delete;
  ~Barrier();

  void wait() const;
  void setNumThreads(uint32_t numThreads);

private:
  std::atomic<kmp_uint32> *barrier;
  uint32_t numThreads;
};
}; // namespace kmp
