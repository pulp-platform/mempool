#include "etl/vector.h"
#include "kmp/thread.hpp"
#include "kmp/types.h"

extern "C" {
#include "runtime.h"
}

namespace kmp {

namespace runtime {

std::array<char, sizeof(Thread) * NUM_CORES> theadBuffer;
etl::vector_ext<kmp::Thread> threads(theadBuffer.data(), NUM_CORES);

} // namespace runtime

} // namespace kmp
