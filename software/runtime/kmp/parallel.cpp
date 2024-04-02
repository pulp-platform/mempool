#include "gomp/omp.h"
#include "kmp.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "barrier.hpp"

kmp_event_t kmp_event;
static volatile uint32_t barrier = 0;

static void __microtask_wrapper(void *arg) {
  kmp_int32 id = mempool_get_core_id();
  kmpc_micro fn = (kmpc_micro)arg;
  fn(&id, &id);
  __kmp_barrier(&barrier, NUM_CORES);
}

int __kmp_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask,
                    va_list ap) {
  kmp_event.fn = &__microtask_wrapper;
  kmp_event.data = (void *)microtask;

  wake_up_all();
  mempool_wfi();

  __kmp_run_task(0);
  return 0;
};

void __kmp_run_task(kmp_int32 gtid) { kmp_event.fn(kmp_event.data); };
