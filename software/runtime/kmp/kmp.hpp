#pragma once

#include "barrier.hpp"
#include "etl/list.h"
#include "etl/optional.h"
#include "etl/vector.h"
#include "printf.h"
#include <etl/functional.h>

extern "C" {
#include "alloc.h"
}

typedef uint32_t kmp_int32;

typedef void (*kmpc_micro)(kmp_int32 *global_tid, kmp_int32 *bound_tid, ...);
typedef void (*kmpc_micro_bound)(kmp_int32 *bound_tid, kmp_int32 *bound_nth,
                                 ...);

namespace kmp {

void errorPrinter(const etl::exception &e);

class Microtask {
public:
  Microtask(kmpc_micro fn, va_list args);
  void run();

private:
  kmpc_micro fn;
  etl::vector<void *, 10> args;
};

class Task {
public:
  Task(Microtask &microtask);
  Task(Microtask &microtask, Barrier &barrier);

  void run();

private:
  Microtask microtask;
  etl::optional<etl::reference_wrapper<Barrier>> barrier;
};

class Thread {
public:
  void run();

public:
  etl::list<Task, 10> tasks;
};

namespace runtime {

void init();

void runThread(kmp_int32 core_id);

extern etl::vector<Thread, NUM_CORES> threads;

} // namespace runtime

} // namespace kmp

typedef struct {
  void (*fn)(void *);
  void *data;
  kmp_int32 nthreads;
  kmp_int32 barrier;
} kmp_event_t;

typedef struct {
  int reserved_1;
  int flags;
  int reserved_2;
  int reserved_3;
  char *psource;
} ident_t;
