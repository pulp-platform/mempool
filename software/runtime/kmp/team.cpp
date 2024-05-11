#include "kmp/team.hpp"
#include "kmp/runtime.hpp"
#include "printf.h"

namespace kmp {

Team::Team(uint32_t numThreads, Task implicitTask)
    : numThreads(numThreads),
      barrier(numThreads), dynamicSchedule{.valid = false},
      implicitTask(std::move(implicitTask)), copyPrivateData(nullptr),
      masterGtid(runtime::getCurrentThread().getGtid()) {

  DEBUG_PRINT("Creating team with %d threads\n", numThreads);

  SharedPointer<Team> sharedThis(this);

  // Make current thread part of the team
  Thread &currentThread = runtime::getCurrentThread();
  threads.push_back(&currentThread);
  currentThread.pushTeam(sharedThis);

  // TODO: I feel like this can be done better

  kmp_uint32 foundThreads = 1;
  for (Thread &thread : runtime::threads) {
    if (foundThreads == numThreads) {
      break;
    }

    if (thread.getGtid() == currentThread.getGtid()) {
    } else if (!thread.isRunning()) { // TODO: Check this
      threads.push_back(&thread);

      thread.pushTeam(sharedThis);

      foundThreads++;
    }
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
