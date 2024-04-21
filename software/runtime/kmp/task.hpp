#pragma once

#include "etl/vector.h"
#include "types.h"

namespace kmp {

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
  Task(const Microtask &microtask);

  void run();

private:
  Microtask microtask;
};
}; // namespace kmp
