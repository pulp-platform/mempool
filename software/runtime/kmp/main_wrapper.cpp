#include "kmp.hpp"
#include "printf.h"

extern "C" {
#include "runtime.h"
}

// https://etherealwake.com/2021/09/crt-startup/
typedef void (*init_func)(void);
extern init_func __init_array_start[];
extern init_func __init_array_end[];

void initGlobals() {
  uint32_t n = __init_array_end - __init_array_start;
  for (size_t i = 0; i < n; i++) {
    __init_array_start[i]();
  }
}

extern "C" int __real_main();

volatile bool initLock = true;

extern "C" int __wrap_main() {
  mempool_id_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    printf("Running OpenMP program on %d cores\n", mempool_get_core_count());

    // Init heap allocators
    mempool_init(0);

    // Call C++ global constructors
    initGlobals();

    // Init OpenMP runtime
    kmp::runtime::init();

    __atomic_and_fetch(&initLock, false, __ATOMIC_SEQ_CST);

    printf("Init done\n");

    // Run the program
    __real_main();

    // Go to sleep since progam is done
    mempool_wfi();
  } else {
    while (__atomic_or_fetch(&initLock, false, __ATOMIC_SEQ_CST)) {
      // printf("Core %d waiting for init, current value: %d\n", core_id, initDone);
      mempool_wait(10);
    }

    kmp::runtime::runThread(core_id);
  }

  return 0;
}
