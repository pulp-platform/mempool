#include "kmp/team.hpp"
#include "kmp/runtime.hpp"
#include "printf.h"

namespace kmp {

Team::Team(kmp_int32 masterGtid, kmp_uint32 numThreads,
           std::optional<Task> implicitTask)
    : numThreads(numThreads), barrier(numThreads),
      dynamicSchedule{.valid = false}, implicitTask(std::move(implicitTask)),
      copyPrivateData(nullptr), masterGtid(masterGtid) {}

} // namespace kmp
