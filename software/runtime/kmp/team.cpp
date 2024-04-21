#include "kmp/team.hpp"
#include "kmp/runtime.hpp"

namespace kmp {

Team::Team(uint32_t numThreads) : numThreads(numThreads), barrier(numThreads) {
  printf("Creating team with %d threads\n", numThreads);

  SharedPointer<Team> sharedThis(this);

  // Make current thread part of the team
  Thread &currentThread = runtime::getCurrentThread();
  threads.push_back(currentThread);
  currentThread.pushTeam(sharedThis);
  tidMap.insert({currentThread.getGtid(), 0});

  kmp_uint32 foundThreads = 1;
  for (Thread &thread : runtime::threads) {
    if (foundThreads == numThreads) {
      break;
    } else if (thread.getGtid() == currentThread.getGtid()) {
    } else if (!thread.isRunning()) { // TODO: Check this
      threads.push_back(thread);
      tidMap.insert({thread.getGtid(), foundThreads});

      thread.pushTeam(sharedThis);

      foundThreads++;
    }
  }

  this->barrier.setNumThreads(foundThreads);
  this->numThreads = foundThreads;
}

void Team::pushTaskAll(const Task &task) const {
  for (Thread &thread : threads) {
    thread.pushTask(task);
    thread.wakeUp();
  }
}

kmp_uint32 Team::getThreadTid(kmp_uint32 gtid) const {
  return tidMap.at(gtid); // TODO: Error handling
}

kmp_uint32 Team::getThreadGtid(kmp_uint32 tid) const {
  return tidMap.find(tid)->first; // TODO: Error handling
}

kmp_uint32 Team::getNumThreads() const { return numThreads; }

void Team::barrierWait() const { barrier.wait(); }

} // namespace kmp
