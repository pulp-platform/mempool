#include "kmp.h"
#include "runtime.h"

void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...) {
  uint32_t core_id = mempool_get_core_id();
  printf("%u\n", core_id);
};

void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk) {
  return;
};

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid) { return; };
