#include "kmp/team.hpp"
#include "kmp/runtime.hpp"
#include "printf.h"

namespace kmp {

Team::Team(kmp_uint32 masterGtid, kmp_uint32 numThreads,
           std::optional<Task> implicitTask)
    : masterGtid(masterGtid), numThreads(numThreads), barrier(numThreads),
      implicitTask(std::move(implicitTask)) {}

} // namespace kmp
