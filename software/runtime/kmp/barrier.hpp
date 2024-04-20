#pragma once

#include "kmp/types.h"
#include <atomic>
#include <stdint.h>

namespace kmp {
class Barrier {
public:
  Barrier(uint32_t numCores);
  Barrier(const Barrier &) = delete;
  Barrier &operator=(const Barrier &) = delete;
  ~Barrier();
  void wait() const;

private:
  std::atomic<kmp_uint32> *barrier;
  uint32_t numCores;
};
}; // namespace kmp
