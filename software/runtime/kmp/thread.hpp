#pragma once

#include "etl/list.h"
#include "etl/optional.h"
#include "mutex.hpp"
#include "task.hpp"
#include "types.h"

namespace kmp {

class Thread {
public:
  Thread(kmp_int32 gtid);
  Thread(const Thread &other);
  void run();
  void wakeUp();
  void pushTask(const Task &task);
  void pushNumThreads(kmp_int32 numThreads);
  void forkCall(const Microtask &microtask);
  kmp_int32 getGtid() const;
  kmp_int32 getTid() const;
  etl::optional<etl::reference_wrapper<const Task>> getCurrentTask();

public:
  etl::list<Task, 10> tasks;

protected:
  kmp_int32 gtid;
  kmp_int32 tid;

private:
  std::atomic<bool> running = false;
  etl::optional<kmp_int32> numThreads;
  Mutex tasksLock;
};
}; // namespace kmp
