#include "barrier.hpp"
#include "runtime.hpp"
#include "task.hpp"
#include "types.h"

extern "C" {
#include "runtime.h"

// Parallel
void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...) {
  printf("Forking call\n");

  va_list ap;
  va_start(ap, microtask);
  kmp::Microtask kmpMicrotask(microtask, ap, argc);
  va_end(ap);

  kmp::runtime::threads[mempool_get_core_id()].forkCall(kmpMicrotask);
};

void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk) {
  return;
};

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid) { return; };

void __kmpc_push_num_threads(ident_t *loc, kmp_int32 global_tid,
                             kmp_int32 num_threads) {
  kmp::runtime::threads[global_tid].pushNumThreads(num_threads);
};

kmp_int32 __kmpc_global_thread_num(ident_t *loc) {
  return mempool_get_core_id();
};

void __kmpc_barrier(ident_t *loc, kmp_int32 global_tid) {
  kmp::runtime::threads[global_tid].getCurrentTask()->get().barrierWait();
};
}
