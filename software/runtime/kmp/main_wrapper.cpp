#include "kmp.hpp"
#include "printf.h"

extern "C" {
#include "runtime.h"
}

extern "C" int __real_main();

extern "C" int __wrap_main() {
  mempool_id_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    printf("Running OpenMP program on %d cores\n", mempool_get_core_count());

    // Init heap allocators
    mempool_init(0);

    // Init OpenMP runtime
    __kmp_init();

    // Run the program
    __real_main();

    // Go to sleep since progam is done
    mempool_wfi();
  } else {
    while (1) {
      mempool_wfi();
      __kmp_run_task(core_id);
    }
  }

  return 0;
}
