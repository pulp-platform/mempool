#pragma once

#include "etl/vector.h"
#include "kmp/util.hpp"
#include "types.h"

namespace kmp {

class Microtask {
public:
  Microtask(kmpc_micro fn, va_list args, kmp_int32 argc);

  Microtask(Microtask &&);
  Microtask &operator=(Microtask &&);

  // Disallow copy constructor and assignment
  Microtask(const Microtask &) = delete;
  Microtask &operator=(const Microtask &) = delete;

  ~Microtask();

  void run() const;

private:
  kmpc_micro fn;
  void **args;
  kmp_int32 argc;
};

class Task {
public:
  Task(const SharedPointer<Microtask> &microtask);

  void run() const;

private:
  SharedPointer<Microtask> microtask;
};
}; // namespace kmp
