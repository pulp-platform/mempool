#include "kmp/thread.hpp"
#include "kmp/runtime.hpp"
#include "kmp/util.hpp"
#include <mutex>

extern "C" {
#include "runtime.h"
}

namespace kmp {

Thread::Thread(kmp_uint32 gtid) : gtid(gtid) {
  // If gtid is 0, the thread is the initial thread and should be running
  if (gtid == 0) {
    running = true;
  } else {
    running = false;
  }
};

Thread::Thread(const Thread &){};

void Thread::run() {
  while (1) {
    while (!running) {
      mempool_wfi();
    }

    std::unique_lock<Mutex> lock(tasksMutex);
    if (tasks.size() > 0) {
      Task &task = tasks.front();
      lock.unlock();

      task.run();

      {
        std::lock_guard<Mutex> lock(teamsMutex);
        teams.top()->barrierWait();
        teams.pop();
      }

      lock.lock();
      tasks.pop_front();
      lock.unlock();
    } else {
      running = false;
      lock.unlock();
    }
  }
};

void Thread::wakeUp() {
  if (running) {
    return;
  } else {
    running = true;
    wake_up(gtid);
  }
};

bool Thread::isRunning() const { return running; };

void Thread::pushTask(const Task &task) {
  std::lock_guard<Mutex> lock(tasksMutex);

  tasks.push_back(task);
};

void Thread::requestNumThreads(kmp_int32 numThreads) {
  this->requestedNumThreads = numThreads;
}

void Thread::forkCall(const SharedPointer<Microtask> &microtask) {
  kmp_uint32 numThreads =
      this->requestedNumThreads.value_or(mempool_get_core_count());
  this->requestedNumThreads.reset();

  DEBUG_PRINT("Forking call with %d threads\n", numThreads);

  kmp::Task task(microtask);
  Team *team = new Team(numThreads); // Do not use shared pointer here since it
                                     // will cause double free
  team->pushTaskAll(task);

  task.run();

  DEBUG_PRINT("Done running task\n");

  std::lock_guard<Mutex> teamsLock(teamsMutex);
  teams.top()->barrierWait();
  teams.pop();

  DEBUG_PRINT("Popped team\n");

  std::lock_guard<Mutex> tasksLock(tasksMutex);
  tasks.pop_front();

  DEBUG_PRINT("Popped task\n");
};

kmp_uint32 Thread::getGtid() const { return gtid; };

kmp_uint32 Thread::getTid() {
  std::lock_guard<Mutex> lock(teamsMutex);

  return teams.size() > 0 ? teams.top()->getThreadTid(gtid)
                          : 0; // If thread is part of no team, assume it is the
                               // inital thread
};

void Thread::pushTeam(SharedPointer<Team> team) {
  std::lock_guard<Mutex> lock(teamsMutex);

  teams.push(team); // TODO: Maybe use std::move here
};

void Thread::popTeam() {
  std::lock_guard<Mutex> lock(teamsMutex);

  teams.pop();
};

SharedPointer<Team> Thread::getCurrentTeam() {
  std::lock_guard<Mutex> lock(teamsMutex);

  return teams.top();
};

etl::optional<etl::reference_wrapper<const Task>> Thread::getCurrentTask() {
  std::lock_guard<Mutex> lock(tasksMutex);

  if (tasks.size() > 0) {
    return etl::cref(tasks.front());
  } else {
    return etl::nullopt;
  }
};

void Thread::copyPrivate(ident_t *loc, kmp_int32 gtid, size_t cpy_size,
                         void *cpy_data, void (*cpy_func)(void *, void *),
                         kmp_int32 didit) {
  auto team = getCurrentTeam();

  if (didit) {
    team->setCopyPrivateData(cpy_data);
    DEBUG_PRINT("Thread %d set copyprivate data to %p\n", gtid, cpy_data);
  }

  team->barrierWait();

  if (!didit) {
    DEBUG_PRINT("Thread %d copying copyprivate data from %p to %p\n", gtid,
                team->getCopyPrivateData(), cpy_data);
    cpy_func(cpy_data, team->getCopyPrivateData());
  }

  team->barrierWait();
};

} // namespace kmp
