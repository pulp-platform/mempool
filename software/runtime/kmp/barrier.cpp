#include "barrier.hpp"
#include "kmp/util.hpp"
#include <cstdint>

namespace kmp {
Barrier::Barrier(uint32_t numThreads) : barrier(), numThreads(numThreads) {}

Barrier::~Barrier() { DEBUG_PRINT("Destroying barrier at %p\n", this); }

}; // namespace kmp
