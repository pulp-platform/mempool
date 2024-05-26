#include "barrier.hpp"

namespace kmp {
Barrier::Barrier(uint32_t numThreads) : barrier(0), numThreads(numThreads) {}

Barrier::~Barrier() { DEBUG_PRINT("Destroying barrier at %p\n", this); }

}; // namespace kmp
