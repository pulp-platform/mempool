// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "libgomp.h"
#include "runtime.h"

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

int __real_main();

int __wrap_main() {
  const mempool_id_t core_id = mempool_get_core_id();

  mempool_barrier_init(core_id);
  mempool_init(core_id);

  if (core_id == 0) {
    initGlobals();
    __real_main();
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
