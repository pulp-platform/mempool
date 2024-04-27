#include "etl/vector.h"
#include "kmp/thread.hpp"
#include "kmp/types.h"

extern "C" {
#include "runtime.h"
}

namespace kmp {

namespace runtime {

etl::vector<kmp::Thread, NUM_CORES> threads;

} // namespace runtime

} // namespace kmp
