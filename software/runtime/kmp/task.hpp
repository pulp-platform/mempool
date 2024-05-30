#pragma once

#include "types.h"
#include <cstdarg>
#include <utility>

#define MAX_ARGS 15

namespace kmp {

class Microtask {
public:
  Microtask(kmpc_micro func, void **args, kmp_int32 argc);

  Microtask(Microtask &&) noexcept;
  Microtask &operator=(Microtask &&) noexcept;

  // Disallow copy constructor and assignment
  Microtask(const Microtask &) = delete;
  Microtask &operator=(const Microtask &) = delete;

  void run() const;

private:
  kmpc_micro func;
  kmp_int32 argc;
  void **args;
};

class Task {
public:
  Task(Microtask microtask) : microtask(std::move(microtask)){};

  inline void run() const { microtask.run(); };

private:
  Microtask microtask;
};
}; // namespace kmp
