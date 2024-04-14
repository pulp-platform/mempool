#include "barrier.hpp"
#include "types.h"
#include "task.hpp"
#include "runtime.hpp"

extern "C" {
#include "runtime.h"

// Parallel
void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...) {
  printf("Forking call\n");

  va_list ap;
  va_start(ap, microtask);
  kmp::Microtask kmpMicrotask(microtask, ap, argc);
  va_end(ap);

  kmp::Barrier barrier(mempool_get_core_count());
  kmp::Task task(kmpMicrotask, barrier);

  auto &thisThread = kmp::runtime::threads[mempool_get_core_id()];

  for (auto &thread : kmp::runtime::threads) {
    thread.pushTask(task);

    if (thread.coreId != thisThread.coreId) {
      thread.wakeUp();
    }
  }

  thisThread.tasks.front().run();
  thisThread.tasks.pop_front();
};

void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk) {
  return;
};

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid) { return; };

void __kmpc_barrier(ident_t *loc, kmp_int32 global_tid) {
  kmp::runtime::threads[global_tid].getCurrentTask()->get().barrierWait();
};
}
