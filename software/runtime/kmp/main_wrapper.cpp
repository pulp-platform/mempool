// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "kmp/runtime.hpp"

extern "C" {
#include "runtime.h"
}

// https://etherealwake.com/2021/09/crt-startup/
typedef void (*init_func)(void);
extern init_func __init_array_start[];
extern init_func __init_array_end[];

static inline void initGlobals() {
  // NOLINTNEXTLINE(*-narrowing-conversions)
  int32_t len = __init_array_end - __init_array_start;
  for (int32_t i = 0; i < len; i++) {

    // NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-pointer-arithmetic)
    __init_array_start[i]();
  }
}

extern "C" int __real_main();

bool initLock = true;

extern "C" int __wrap_main() {
  const mempool_id_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    DEBUG_PRINT("Running OpenMP program on %d cores\n",
                mempool_get_core_count());

    // Init heap allocators
    mempool_init(0);

    // Call C++ global constructors
    initGlobals();

    initLock = false;

    DEBUG_PRINT("Init done\n");

    // Run the program
    __real_main();

    printf("Program done\n");
  } else {
    while (initLock) {
      // Wait for initialization to finish
    }

    kmp::runtime::runThread(static_cast<kmp_int32>(core_id));
  }

  return 0;
}
