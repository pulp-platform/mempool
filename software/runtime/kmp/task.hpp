// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "types.h"
#include <utility>

#define MAX_ARGS 15

namespace kmp {

class Microtask {
public:
  Microtask(kmpc_micro func, void **args, kmp_int32 argc);

  Microtask(Microtask &&) noexcept;
  Microtask &operator=(Microtask &&) noexcept;

  ~Microtask() = default;

  // Disallow copy constructor and assignment
  Microtask(const Microtask &) = default;
  Microtask &operator=(const Microtask &) = default;

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
