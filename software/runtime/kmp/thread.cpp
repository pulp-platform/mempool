#include "thread.hpp"
#include "mutex.hpp"
#include <mutex>

extern "C" {
#include "runtime.h"
}

namespace kmp {

Thread::Thread(const Thread &other){};

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
    wake_up(coreId);
  }
};

void Thread::pushTask(const Task &task) {
  std::lock_guard<Mutex> lock(tasksLock);

  tasks.push_back(task);
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
