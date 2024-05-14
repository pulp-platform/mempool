#include "kmp/team.hpp"
#include "kmp/runtime.hpp"
#include "printf.h"

namespace kmp {

Team::Team(uint32_t numThreads, Task implicitTask)
    : numThreads(numThreads), barrier(numThreads),
      dynamicSchedule{.valid = false}, implicitTask(std::move(implicitTask)),
      copyPrivateData(nullptr),
      masterGtid(runtime::getCurrentThread().getGtid()) {

  SharedPointer<Team> sharedThis(this);
  DEBUG_PRINT("Creating team with %d threads at %p\n", numThreads, this);

  // Make current thread part of the team
  Thread &currentThread = runtime::getCurrentThread();
  this->threads.push_back(&currentThread);
  currentThread.setCurrentTeam(sharedThis);

  kmp_uint32 foundThreads = 1;
  for (Thread &thread : runtime::threads) {
    if (foundThreads == numThreads) {
      break;
    }

    if (thread.getGtid() == currentThread.getGtid()) {
      continue;
    }

    if (thread.isRunning()) {
      continue;
    }

    thread.setCurrentTeam(sharedThis);
    DEBUG_PRINT("Pushing thread %d to team\n", thread.getGtid());

    thread.setTid(foundThreads);

    this->threads.push_back(&thread);
    DEBUG_PRINT("Done pushing thread %d to team\n", thread.getGtid());

    foundThreads++;
  }

  this->barrier.setNumThreads(foundThreads);
  this->numThreads = foundThreads;

  for (Thread *thread : threads) {
    thread->wakeUp();
  }

  DEBUG_PRINT("Team created with %d threads\n", numThreads);
}

void Team::pushTaskAll(Task task) const {
  for (Thread *thread : threads) {
    thread->pushTask(std::move(task));
    thread->wakeUp();
  }
}

} // namespace kmp
