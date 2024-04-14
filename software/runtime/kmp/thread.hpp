#pragma once

#include "etl/optional.h"
#include "etl/list.h"
#include "mutex.hpp"
#include "task.hpp"
#include "types.h"

namespace kmp {

class Thread {
public:
  Thread() = default;
  Thread(const Thread &other);
  void run();
  void wakeUp();
  void pushTask(const Task &task);
  etl::optional<etl::reference_wrapper<const Task>> getCurrentTask();

public:
  kmp_int32 coreId;
  etl::list<Task, 10> tasks;

private:
  std::atomic<bool> running = false;
  Mutex tasksLock;
};
}; // namespace kmp
