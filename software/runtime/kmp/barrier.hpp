#pragma once

#include "kmp/types.h"
#include <atomic>
#include <stdint.h>

namespace kmp {
class Barrier {
public:
  Barrier(uint32_t numCores);
  Barrier(const Barrier &other);
  ~Barrier();
  void wait() const;

private:
  std::atomic<kmp_uint32> *barrier;
  std::atomic<kmp_uint32> *counter;
  uint32_t numCores;
};
}; // namespace kmp
