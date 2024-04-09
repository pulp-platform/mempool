#pragma once

#include <cstdint>

typedef uint32_t kmp_int32;

typedef void (*kmpc_micro)(kmp_int32 *global_tid, kmp_int32 *bound_tid, ...);
typedef void (*kmpc_micro_bound)(kmp_int32 *bound_tid, kmp_int32 *bound_nth,
                                 ...);

typedef struct {
  void (*fn)(void *);
  void *data;
  kmp_int32 nthreads;
  kmp_int32 barrier;
} kmp_event_t;

extern kmp_event_t kmp_event;

typedef struct {
  int reserved_1;
  int flags;
  int reserved_2;
  int reserved_3;
  char *psource;
} ident_t;

#ifdef __cplusplus
extern "C" {
#endif

// C interface
void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...);

void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk);

void __kmpc_barrier(ident_t *loc, kmp_int32 global_tid);

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid);

// C++ interface
void __kmp_init();

void __kmp_run_task(kmp_int32 gtid);

#ifdef __cplusplus
}
#endif
