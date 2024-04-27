#pragma once

#include "etl/vector.h"
#include "kmp/thread.hpp"
#include "kmp/types.h"

namespace kmp::runtime {

extern etl::vector<Thread, NUM_CORES> threads;

static inline void assertWrapper(const etl::exception &e) {
  __assert_func(e.file_name(), e.line_number(), "n/a", e.what());
};

static inline void init() {
  printf("Initializing runtime\n");

#ifdef ETL_LOG_ERRORS
  etl::error_handler::set_callback<assertWrapper>();
#endif

  for (kmp_uint32 i = 0; i < NUM_CORES; i++) {
    threads.emplace_back(i);
  }
};

static inline void runThread(kmp_uint32 core_id) { threads[core_id].run(); };

static inline Thread &getCurrentThread() { return threads[mempool_get_core_id()]; };

} // namespace kmp::runtime
