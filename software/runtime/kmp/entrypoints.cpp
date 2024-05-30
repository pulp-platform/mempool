#include "kmp/runtime.hpp"
#include "kmp/team.hpp"
#include "kmp/types.h"

using kmp::Mutex;

extern "C" {
#include "runtime.h"

void __kmpc_barrier(ident_t * /*loc*/, kmp_int32 global_tid) {
  kmp::runtime::getCurrentThread(static_cast<kmp_uint32>(global_tid))
      .getCurrentTeam()
      ->getBarrier()
      .wait();
};

// Parallel
void __kmpc_fork_call(ident_t * /*loc*/, kmp_int32 argc, kmpc_micro microtask,
                      ...) {
  // NOLINTBEGIN(cppcoreguidelines-pro-bounds-array-to-pointer-decay,
  // cppcoreguidelines-pro-type-reinterpret-cast)
  va_list args;
  va_start(args, microtask);
  kmp::Microtask kmpMicrotask(microtask, reinterpret_cast<void **>(args), argc);
  kmp::runtime::getCurrentThread().forkCall(std::move(kmpMicrotask));
  va_end(args);
  // NOLINTEND(cppcoreguidelines-pro-bounds-array-to-pointer-decay,
  // cppcoreguidelines-pro-type-reinterpret-cast)
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

void __kmpc_for_static_init_8(ident_t * /*loc*/, kmp_int32 /*gtid*/,
                              kmp_int32 /*schedtype*/,
                              kmp_int64 * /*plastiter*/, kmp_int64 * /*plower*/,
                              kmp_int64 * /*pupper*/, kmp_int64 * /*pstride*/,
                              kmp_int64 /*incr*/, kmp_int64 /*chunk*/) {
  assert(false && "Unsupported loop index type");
};

void __kmpc_for_static_init_8u(ident_t * /*loc*/, kmp_int32 /*gtid*/,
                               kmp_int32 /*schedtype*/,
                               kmp_uint64 * /*plastiter*/,
                               kmp_uint64 * /*plower*/, kmp_uint64 * /*pupper*/,
                               kmp_int64 * /*pstride*/, kmp_int64 /*incr*/,
                               kmp_int64 /*chunk*/) {
  assert(false && "Unsupported loop index type");
};

void __kmpc_for_static_fini(ident_t * /*loc*/, kmp_int32 /*global_tid*/){};

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

void __kmpc_dispatch_init_8(ident_t * /*loc*/, kmp_int64 /*gtid*/,
                            kmp_sched_type /*schedtype*/, kmp_int64 /*lower*/,
                            kmp_int64 /*upper*/, kmp_int64 /*incr*/,
                            kmp_int64 /*chunk*/) {
  assert(false && "Unsupported loop index type");
}

void __kmpc_dispatch_init_8u(ident_t * /*loc*/, kmp_int64 /*gtid*/,
                             kmp_sched_type /*schedtype*/, kmp_uint64 /*lower*/,
                             kmp_uint64 /*upper*/, kmp_int64 /*incr*/,
                             kmp_int64 /*chunk*/) {
  assert(false && "Unsupported loop index type");
}

int __kmpc_dispatch_next_4(ident_t *loc, kmp_int32 gtid, kmp_int32 *plastiter,
                           kmp_int32 *plower, kmp_int32 *pupper,
                           kmp_int32 *pstride) {
  return static_cast<int>(
      kmp::runtime::getCurrentThread().getCurrentTeam()->dispatchNext(
          loc, gtid, plastiter, plower, pupper, pstride));
}

int __kmpc_dispatch_next_4u(ident_t *loc, kmp_int32 gtid, kmp_int32 *plastiter,
                            kmp_uint32 *plower, kmp_uint32 *pupper,
                            kmp_int32 *pstride) {
  return static_cast<int>(
      kmp::runtime::getCurrentThread().getCurrentTeam()->dispatchNext(
          loc, gtid, plastiter, plower, pupper, pstride));
}

int __kmpc_dispatch_next_8(ident_t * /*loc*/, kmp_int64 /*gtid*/,
                           kmp_int64 * /*plastiter*/, kmp_int64 * /*plower*/,
                           kmp_int64 * /*pupper*/, kmp_int64 * /*pstride*/) {
  assert(false && "Unsupported loop index type");
}

int __kmpc_dispatch_next_8u(ident_t * /*loc*/, kmp_int64 /*gtid*/,
                            kmp_int64 * /*plastiter*/, kmp_uint64 * /*plower*/,
                            kmp_uint64 * /*pupper*/, kmp_int64 * /*pstride*/) {
  assert(false && "Unsupported loop index type");
}

void __kmpc_push_num_threads(ident_t * /*loc*/, kmp_int32 /*global_tid*/,
                             kmp_int32 num_threads) {
  kmp::runtime::getCurrentThread().requestNumThreads(num_threads);
};

// Critical sections
void __kmpc_critical(ident_t * /*unused*/, kmp_int32 /*gtid*/,
                     kmp_critical_name *crit) {
  static_assert(sizeof(kmp::Mutex) <= sizeof(kmp_critical_name));

  // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
  kmp::Mutex *mutex = reinterpret_cast<kmp::Mutex *>(*crit);
  mutex->lock();
};

void __kmpc_end_critical(ident_t * /*unused*/, kmp_int32 /*gtid*/,
                         kmp_critical_name *crit) {

  // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
  Mutex *mutex = reinterpret_cast<kmp::Mutex *>(*crit);
  mutex->unlock();
};

// Master
kmp_int32 __kmpc_master(ident_t * /*loc*/, kmp_int32 /*gtid*/) {
  return static_cast<kmp_int32>(kmp::runtime::getCurrentThread().getTid() == 0);
};

void __kmpc_end_master(ident_t * /*loc*/, kmp_int32 /*gtid*/){/* NOOP */};

// Single (same as master for now)
kmp_int32 __kmpc_single(ident_t * /*loc*/, kmp_int32 /*gtid*/) {
  return static_cast<kmp_int32>(kmp::runtime::getCurrentThread().getTid() == 0);
};

void __kmpc_end_single(ident_t * /*loc*/, kmp_int32 /*gtid*/){/* NOOP */};

// Copyprivate
void __kmpc_copyprivate(ident_t *loc, kmp_int32 gtid, size_t cpy_size,
                        void *cpy_data, void (*cpy_func)(void *, void *),
                        kmp_int32 didit) {
  kmp::runtime::getCurrentThread().copyPrivate(loc, gtid, cpy_size, cpy_data,
                                               cpy_func, didit);
};

// Reduction
kmp_int32 __kmpc_reduce_nowait(ident_t * /*loc*/, kmp_int32 /*global_tid*/,
                               kmp_int32 /*num_vars*/, size_t /*reduce_size*/,
                               void * /*reduce_data*/,
                               void (* /*reduce_func*/)(void *lhs_data,
                                                        void *rhs_data),
                               kmp_critical_name * /*lck*/) {
  return 2; // Atomic reduction
}

void __kmpc_end_reduce_nowait(ident_t * /*loc*/, kmp_int32 /*global_tid*/,
                              kmp_critical_name * /*lck*/) {
  /* NOOP */
}

kmp_int32 __kmpc_reduce(ident_t *loc, kmp_int32 global_tid, kmp_int32 num_vars,
                        size_t reduce_size, void *reduce_data,
                        void (*reduce_func)(void *lhs_data, void *rhs_data),
                        kmp_critical_name *lck) {

  return __kmpc_reduce_nowait(loc, global_tid, num_vars, reduce_size,
                              reduce_data, reduce_func, lck);
}

void __kmpc_end_reduce(ident_t *loc, kmp_int32 global_tid,
                       kmp_critical_name * /*lck*/) {
  return __kmpc_barrier(loc, global_tid);
}

// Teams
void __kmpc_fork_teams(ident_t * /*loc*/, kmp_int32 argc, kmpc_micro microtask,
                       ...) {
  // NOLINTBEGIN(cppcoreguidelines-pro-bounds-array-to-pointer-decay,
  // cppcoreguidelines-pro-type-reinterpret-cast)
  va_list args;
  va_start(args, microtask);
  kmp::Microtask kmpMicrotask(microtask, reinterpret_cast<void **>(args), argc);
  kmp::runtime::getCurrentThread().forkTeams(std::move(kmpMicrotask));
  va_end(args);
  // NOLINTEND(cppcoreguidelines-pro-bounds-array-to-pointer-decay,
  // cppcoreguidelines-pro-type-reinterpret-cast)
}

kmp_int32 __kmpc_global_thread_num(ident_t * /*loc*/) {
  return static_cast<kmp_int32>(mempool_get_core_id());
};
}
