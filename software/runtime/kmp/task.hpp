#pragma once

#include "types.h"
#include <cstdarg>

#define MAX_ARGS 15

namespace kmp {

class Microtask {
public:
  Microtask(kmpc_micro func, va_list args, kmp_int32 argc);

  Microtask(Microtask &&) noexcept;
  Microtask &operator=(Microtask &&) noexcept;

  // Disallow copy constructor and assignment
  Microtask(const Microtask &) = delete;
  Microtask &operator=(const Microtask &) = delete;

  ~Microtask();

  void run() const;

private:
  kmpc_micro func;
  void **args;
  kmp_int32 argc;
};

class Task {
public:
  Task(Microtask microtask);

  void run() const;

private:
  Microtask microtask;
};
}; // namespace kmp
