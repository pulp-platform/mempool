#pragma once

#include "kmp/thread.hpp"
#include "kmp/types.h"
#include "etl/error_handler.h"

extern "C" {
#include "runtime.h"
}

// NOLINTNEXTLINE(bugprone-reserved-identifier)
extern void __assert_func(const char *file, int line, const char *func,
                          const char *failedexpr);
static inline void assertWrapper(const etl::exception &e) {
  __assert_func(e.file_name(), e.line_number(), "n/a", e.what());
};

namespace kmp {

namespace runtime {

extern std::array<Thread, NUM_CORES> threads;

extern Team defaultTeam;

static inline void init() {
  printf("Initializing runtime\n");

#ifdef ETL_LOG_ERRORS
  etl::error_handler::set_callback<assertWrapper>();
#endif
};

static inline void runThread(kmp_uint32 core_id) { threads[core_id].run(); };

static inline Thread &getCurrentThread(kmp_int32 gtid) {
  return threads[gtid];
};

static inline Thread &getCurrentThread() {
  return threads[mempool_get_core_id()];
};

} // namespace runtime

} // namespace kmp
