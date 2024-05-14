#include "kmp/thread.hpp"
#include "kmp/runtime.hpp"
#include "kmp/util.hpp"
#include <mutex>

extern "C" {
#include "runtime.h"
}

namespace kmp {

Thread::Thread(kmp_uint32 gtid, kmp_uint32 tid) : gtid(gtid), tid(tid) {
  // If gtid is 0, the thread is the initial thread and should be running
  if (gtid == 0) {
    running = true;
  } else {
    running = false;
  }
};

Thread::Thread(kmp_uint32 gtid) : Thread(gtid, 0) {};

void Thread::run() {
  while (true) {
    while (!running) {
      mempool_wfi();
    }

    const Task &task = currentTeam->getImplicitTask();

    task.run();
    DEBUG_PRINT("Done running task\n", gtid);
    currentTeam->getBarrier().wait();

    currentTeam.reset();
    tid = 0;

    running = false;
  }
};

void Thread::wakeUp() {
  if (running) {
    return;
  }

  running = true;
  wake_up(gtid);
};

bool Thread::isRunning() const { return running; };

void Thread::pushTask(Task task) { tasks.push_back(std::move(task)); };

void Thread::requestNumThreads(kmp_int32 numThreads) {
  this->requestedNumThreads = numThreads;
}

void Thread::forkCall(Microtask microtask) {
  kmp_uint32 numThreads =
      this->requestedNumThreads.value_or(mempool_get_core_count());
  this->requestedNumThreads.reset();

  DEBUG_PRINT("Forking call with %d threads\n", numThreads);

  kmp::Task task(std::move(microtask));
  Team *team =
      new Team(numThreads, std::move(task)); // Do not use shared pointer here
                                             // since it will cause double free

  // team->pushTaskAll(task);

  team->getImplicitTask().run();

  DEBUG_PRINT("Done running task\n");

  // std::lock_guard<Mutex> teamsLock(teamsMutex);
  // teams.top()->barrierWait();
  // teams.pop();

  team->getBarrier().wait();

  // DEBUG_PRINT("Popped team\n");

  // std::lock_guard<Mutex> tasksLock(tasksMutex);
  // tasks.pop_front();

  // DEBUG_PRINT("Popped task\n");
  currentTeam.reset();
};

// void Thread::pushTeam(SharedPointer<Team> team) {
// teams.push(std::move(team));
// };

// void Thread::popTeam() { teams.pop(); };

etl::optional<etl::reference_wrapper<const Task>> Thread::getCurrentTask() {
  if (!tasks.empty()) {
    return etl::cref(tasks.front());
  }

  return etl::nullopt;
};

void Thread::copyPrivate(ident_t *loc, kmp_int32 gtid, size_t cpy_size,
                         void *cpy_data, void (*cpy_func)(void *, void *),
                         kmp_int32 didit) {
  auto team = getCurrentTeam();

  if (didit != 0) {
    team->setCopyPrivateData(cpy_data);
    DEBUG_PRINT("Thread %d set copyprivate data to %p\n", gtid, cpy_data);
  }

  team->getBarrier().wait();

  if (didit == 0) {
    DEBUG_PRINT("Thread %d copying copyprivate data from %p to %p\n", gtid,
                team->getCopyPrivateData(), cpy_data);
    cpy_func(cpy_data, team->getCopyPrivateData());
  }

  team->getBarrier().wait();
};

} // namespace kmp
