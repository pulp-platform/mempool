#include "kmp/team.hpp"
#include "kmp/runtime.hpp"
#include "printf.h"

namespace kmp {

Team::Team(kmp_int32 masterGtid, uint32_t numThreads, Task implicitTask)
    : numThreads(numThreads), barrier(numThreads),
      dynamicSchedule{.valid = false}, implicitTask(std::move(implicitTask)),
      copyPrivateData(nullptr), masterGtid(masterGtid) {

  SharedPointer<Team> sharedThis(this);
  DEBUG_PRINT("Creating team with %d threads at %p\n", numThreads, this);
  DEBUG_PRINT("Team barrier at %p\n", &this->barrier);

  // Make current thread part of the team
  Thread &currentThread = runtime::getCurrentThread(masterGtid);

  // this->threads.reserve(numThreads);
  // this->threads.push_back(&currentThread);
  currentThread.setCurrentTeam(sharedThis);

  kmp_uint32 foundThreads = 1;
  for (kmp_uint32 i = 1; i < numThreads && foundThreads < numThreads; i++) {
    if (i == masterGtid) {
      continue;
    }

    Thread &thread = runtime::threads[i];

    if (thread.isRunning()) {
      continue;
    }

    thread.setCurrentTeam(sharedThis);
    DEBUG_PRINT("Pushing thread %d to team\n", thread.getGtid());

    thread.setTid(foundThreads);

    thread.wakeUp();

    // this->threads.push_back(&thread);
    DEBUG_PRINT("Done pushing thread %d to team\n", thread.getGtid());

    foundThreads++;
  }

  this->barrier.setNumThreads(foundThreads);
  this->numThreads = foundThreads;

  DEBUG_PRINT("Team created with %d threads\n", foundThreads);
  this->ready = true;
}

} // namespace kmp
