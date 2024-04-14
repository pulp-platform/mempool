#include "thread.hpp"
#include "mutex.hpp"
#include "runtime.hpp"
#include <mutex>

extern "C" {
#include "runtime.h"
}

namespace kmp {

Thread::Thread(kmp_int32 gtid) : gtid(gtid) {};

Thread::Thread(const Thread &){};

void Thread::run() {
  while (1) {
    while (!running) {
      mempool_wfi();
    }

    tasksLock.lock();
    if (tasks.size() > 0) {
      Task &task = tasks.front();
      tasksLock.unlock();

      task.run();

      tasksLock.lock();
      tasks.pop_front();
      tasksLock.unlock();
    } else {
      running = false;
      tasksLock.unlock();
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

void Thread::pushTask(const Task &task) {
  std::lock_guard<Mutex> lock(tasksLock);

  tasks.push_back(task);
};

void Thread::pushNumThreads(kmp_int32 numThreads) {
  this->numThreads = numThreads;
}

void Thread::forkCall(const Microtask &microtask) {
  auto numThreads = this->numThreads.value_or(mempool_get_core_count());
  this->numThreads.reset();

  printf("Forking call with %d threads\n", numThreads);

  kmp::Task task(microtask, numThreads);

  for (kmp_int32 tid = 0; tid < numThreads; tid++) {
    Thread &thread = kmp::runtime::threads[tid];
    thread.pushTask(task);
    thread.tid = tid;

    if (thread.gtid != this->gtid) {
      thread.wakeUp();
    }
  }

  task.run();

  std::lock_guard<Mutex> lock(tasksLock);
  tasks.pop_front();
};

kmp_int32 Thread::getGtid() const {
  return gtid;
};

kmp_int32 Thread::getTid() const {
  return tid;
};

etl::optional<etl::reference_wrapper<const Task>> Thread::getCurrentTask() {
  std::lock_guard<Mutex> lock(tasksLock);

  if (tasks.size() > 0) {
    return etl::cref(tasks.front());
  } else {
    return etl::nullopt;
  }
};
} // namespace kmp
