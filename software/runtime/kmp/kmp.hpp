#pragma once

#include "barrier.hpp"
#include "etl/list.h"
#include "etl/optional.h"
#include "etl/vector.h"
#include "mutex.hpp"
#include "printf.h"
#include <etl/functional.h>

extern "C" {
#include "alloc.h"
}

typedef uint32_t kmp_int32;

typedef void (*kmpc_micro)(kmp_int32 *global_tid, kmp_int32 *bound_tid, ...);
typedef void (*kmpc_micro_bound)(kmp_int32 *bound_tid, kmp_int32 *bound_nth,
                                 ...);

typedef struct {
  int reserved_1;
  int flags;
  int reserved_2;
  int reserved_3;
  char *psource;
} ident_t;

namespace kmp {

void errorPrinter(const etl::exception &e);

class Microtask {
public:
  Microtask(kmpc_micro fn, va_list args, kmp_int32 argc);
  void run();

private:
  kmpc_micro fn;
  etl::vector<void *, 15> args;
};

class Task {
public:
  Task(const Microtask &microtask, Barrier &barrier);

  void run();
  void barrierWait() const;

private:
  Microtask microtask;
  etl::reference_wrapper<Barrier> barrier;
};

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

namespace runtime {

void init();

void runThread(kmp_int32 core_id);

extern etl::vector<Thread, NUM_CORES> threads;

} // namespace runtime

} // namespace kmp
