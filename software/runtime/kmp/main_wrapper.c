#include "printf.h"
#include "runtime.h"

int __real_main();

int __wrap_main() {
  mempool_id_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    return __real_main();
  } else {
    // TODO: Fetch work
    return 0;
  }
}
