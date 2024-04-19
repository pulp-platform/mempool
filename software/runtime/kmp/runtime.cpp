#include "etl/vector.h"
#include "kmp/thread.hpp"
#include "kmp/types.h"

extern "C" {
#include "runtime.h"
}

namespace kmp {

namespace runtime {

etl::vector<kmp::Thread, NUM_CORES> threads;

void assertWrapper(const etl::exception &e) {
  __assert_func(e.file_name(), e.line_number(), "n/a", e.what());
};

void init() {
  printf("Initializing runtime\n");

#ifdef ETL_LOG_ERRORS
  etl::error_handler::set_callback<assertWrapper>();
#endif

  for (kmp_uint32 i = 0; i < NUM_CORES; i++) {
    threads.emplace_back(i);
  }
};

void runThread(kmp_uint32 core_id) { threads[core_id].run(); };

Thread &getCurrentThread() { return threads[mempool_get_core_id()]; };

} // namespace runtime

} // namespace kmp
