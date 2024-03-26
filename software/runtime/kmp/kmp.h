
#include "stdint.h"

typedef struct {
  int reserved_1;
  int flags;
  int reserved_2;
  int reserved_3;
  char *psource;
} ident_t;

typedef uint32_t kmp_int32;

typedef void (*kmpc_micro)(kmp_int32 *global_tid, kmp_int32 *bound_tid, ...);
typedef void (*kmpc_micro_bound)(kmp_int32 *bound_tid, kmp_int32 *bound_nth,
                                 ...);

#ifdef __cplusplus
extern "C" {
#endif

void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...);

void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk);

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid);

#ifdef __cplusplus
}
#endif
