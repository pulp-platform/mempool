#include "barrier.hpp"
#include "kmp/util.hpp"
#include <cstdint>

namespace kmp {
Barrier::Barrier(uint32_t numThreads)
    : barrier(new std::atomic<kmp_uint32>(0)), numThreads(numThreads) {}

Barrier::~Barrier() {
  DEBUG_PRINT("Destroying barrier at %p\n", this);
  delete barrier;
}

}; // namespace kmp
