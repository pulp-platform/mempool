#include "kmp.h"
#include "printf.h"
#include "runtime.h"

// Parallel

void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...) {
  va_list ap;
  va_start(ap, microtask);

  __kmp_fork_call(loc, argc, microtask, ap);
};

void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk) {
  return;
};

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid) { return; };
