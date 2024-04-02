#pragma once

#include "stdarg.h"
#include "stdint.h"

#ifndef NUM_THREADS
#define NUM_THREADS 1
#endif

typedef struct {
  void (*fn)(void *);
  void *data;
} kmp_event_t;

extern kmp_event_t kmp_event;

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

int __kmp_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask,
                    va_list ap);

void __kmp_run_task(kmp_int32 gtid);

#ifdef __cplusplus
}
#endif
