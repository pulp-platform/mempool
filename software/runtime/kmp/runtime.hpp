#pragma once

#include "etl/vector.h"
#include "kmp/thread.hpp"
#include "kmp/types.h"

namespace kmp::runtime {

void init();

void runThread(kmp_uint32 core_id);

Thread &getCurrentThread();

extern etl::vector<Thread, NUM_CORES> threads;

} // namespace kmp::runtime
