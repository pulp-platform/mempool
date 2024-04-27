#include "kmp/runtime.hpp"
#include "kmp/task.hpp"
#include "kmp/thread.hpp"
#include "kmp/types.h"

extern "C" {
#include "runtime.h"

void __kmpc_barrier(ident_t *loc, kmp_int32 global_tid) {
  kmp::runtime::getCurrentThread().getCurrentTeam()->barrierWait();
};

// Parallel
void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...) {
  va_list ap;
  va_start(ap, microtask);
  kmp::SharedPointer<kmp::Microtask> kmpMicrotask(new kmp::Microtask(microtask, ap, argc));
  va_end(ap);

  kmp::runtime::getCurrentThread().forkCall(kmpMicrotask);
};

// Static loops
void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int32 *plastiter, kmp_int32 *plower,
                              kmp_int32 *pupper, kmp_int32 *pstride,
                              kmp_int32 incr, kmp_int32 chunk) {
  kmp::runtime::getCurrentThread().getCurrentTeam()->forStaticInit(
      loc, gtid, static_cast<kmp_sched_type>(schedtype), plastiter, plower,
      pupper, pstride, incr, chunk);
};

void __kmpc_for_static_init_4u(ident_t *loc, kmp_int32 gtid,
                               kmp_int32 schedtype, kmp_uint32 *plastiter,
                               kmp_uint32 *plower, kmp_uint32 *pupper,
                               kmp_int32 *pstride, kmp_int32 incr,
                               kmp_int32 chunk) {
  kmp::runtime::getCurrentThread().getCurrentTeam()->forStaticInit(
      loc, gtid, static_cast<kmp_sched_type>(schedtype), plastiter, plower,
      pupper, pstride, incr, chunk);
};

void __kmpc_for_static_init_8(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                              kmp_int64 *plastiter, kmp_int64 *plower,
                              kmp_int64 *pupper, kmp_int64 *pstride,
                              kmp_int64 incr, kmp_int64 chunk) {
  assert(false && "Unsupported loop index type");
};

void __kmpc_for_static_init_8u(ident_t *loc, kmp_int32 gtid,
                               kmp_int32 schedtype, kmp_uint64 *plastiter,
                               kmp_uint64 *plower, kmp_uint64 *pupper,
                               kmp_int64 *pstride, kmp_int64 incr,
                               kmp_int64 chunk) {
  assert(false && "Unsupported loop index type");
};

void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid) {
  __kmpc_barrier(loc, global_tid);
};

// Dynamic loops
void __kmpc_dispatch_init_4(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                            kmp_int32 lower, kmp_int32 upper, kmp_int32 incr,
                            kmp_int32 chunk) {
  kmp::runtime::getCurrentThread().getCurrentTeam()->dispatchInit(
      loc, gtid,
      static_cast<kmp_sched_type>(SCHEDULE_WITHOUT_MODIFIERS(schedtype)), lower,
      upper, incr, chunk);
}

void __kmpc_dispatch_init_4u(ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype,
                             kmp_uint32 lower, kmp_uint32 upper, kmp_int32 incr,
                             kmp_int32 chunk) {
  kmp::runtime::getCurrentThread().getCurrentTeam()->dispatchInit(
      loc, gtid,
      static_cast<kmp_sched_type>(SCHEDULE_WITHOUT_MODIFIERS(schedtype)), lower,
      upper, incr, chunk);
}

void __kmpc_dispatch_init_8(ident_t *loc, kmp_int64 gtid,
                            kmp_sched_type schedtype, kmp_int64 lower,
                            kmp_int64 upper, kmp_int64 incr, kmp_int64 chunk) {
  assert(false && "Unsupported loop index type");
}

void __kmpc_dispatch_init_8u(ident_t *loc, kmp_int64 gtid,
                             kmp_sched_type schedtype, kmp_uint64 lower,
                             kmp_uint64 upper, kmp_int64 incr,
                             kmp_int64 chunk) {
  assert(false && "Unsupported loop index type");
}

int __kmpc_dispatch_next_4(ident_t *loc, kmp_int32 gtid, kmp_int32 *plastiter,
                           kmp_int32 *plower, kmp_int32 *pupper,
                           kmp_int32 *pstride) {
  return kmp::runtime::getCurrentThread().getCurrentTeam()->dispatchNext(
      loc, gtid, plastiter, plower, pupper, pstride);
}

int __kmpc_dispatch_next_4u(ident_t *loc, kmp_int32 gtid, kmp_int32 *plastiter,
                            kmp_uint32 *plower, kmp_uint32 *pupper,
                            kmp_int32 *pstride) {
  return kmp::runtime::getCurrentThread().getCurrentTeam()->dispatchNext(
      loc, gtid, plastiter, plower, pupper, pstride);
}

int __kmpc_dispatch_next_8(ident_t *loc, kmp_int64 gtid, kmp_int64 *plastiter,
                           kmp_int64 *plower, kmp_int64 *pupper,
                           kmp_int64 *pstride) {
  assert(false && "Unsupported loop index type");
}

int __kmpc_dispatch_next_8u(ident_t *loc, kmp_int64 gtid, kmp_int64 *plastiter,
                            kmp_uint64 *plower, kmp_uint64 *pupper,
                            kmp_int64 *pstride) {
  assert(false && "Unsupported loop index type");
}

void __kmpc_push_num_threads(ident_t *loc, kmp_int32 global_tid,
                             kmp_int32 num_threads) {
  kmp::runtime::getCurrentThread().requestNumThreads(num_threads);
};

kmp_int32 __kmpc_global_thread_num(ident_t *loc) {
  return mempool_get_core_id();
};
}
