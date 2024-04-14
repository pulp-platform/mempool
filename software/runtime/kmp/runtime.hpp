#pragma once

#include "etl/vector.h"
#include "thread.hpp"
#include "types.h"

namespace kmp::runtime {

void init();

void runThread(kmp_int32 core_id);

extern etl::vector<Thread, NUM_CORES> threads;

} // namespace runtime

