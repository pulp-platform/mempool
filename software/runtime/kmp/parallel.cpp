#include "barrier.hpp"
#include "kmp.h"
#include "omp.h"
#include "printf.h"

extern "C" {
#include "runtime.h"
}

kmp_event_t kmp_event;
static volatile uint32_t barrier = 0;

static void __microtask_wrapper(void *arg) {
  kmp_int32 id = mempool_get_core_id();
  kmpc_micro fn = (kmpc_micro)arg;
  fn(&id, &id);
  __kmp_barrier(&barrier, mempool_get_core_count());
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

void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk);

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid);

void __kmp_run_task(kmp_int32 gtid) { kmp_event.fn(kmp_event.data); };
