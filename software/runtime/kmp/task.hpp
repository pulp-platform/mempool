// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "types.h"

#define MAX_ARGS 15

namespace kmp {

class Task {
public:
  Task(kmpc_micro func, void **args, kmp_int32 argc);

  void run(kmp_int32 gtid, kmp_int32 tid) const;

private:
  kmpc_micro func;
  kmp_int32 argc;
  void **args;
};

}; // namespace kmp
