#pragma once

#include "etl/error_handler.h"
#include "kmp/thread.hpp"
#include "kmp/types.h"

// NOLINTNEXTLINE(bugprone-reserved-identifier)
extern void __assert_func(const char *file, int line, const char *func,
                          const char *failedexpr);

static inline void assertWrapper(const etl::exception &exception) {
  __assert_func(exception.file_name(), exception.line_number(), "n/a",
                exception.what());
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

static inline Thread &getCurrentThread(kmp_uint32 gtid) {
  return threads[gtid];
};

static inline Thread &getCurrentThread() {
  return threads[mempool_get_core_id()];
};

} // namespace runtime

} // namespace kmp
