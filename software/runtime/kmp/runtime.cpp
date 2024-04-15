#include "etl/vector.h"
#include "kmp/thread.hpp"
#include "kmp/types.h"
#include "printf.h"

extern "C" {
#include "runtime.h"
}

namespace kmp {

namespace runtime {

etl::vector<kmp::Thread, NUM_CORES> threads;

void printError(const etl::exception &e) {
  printf("%s %s %d\n", e.what(), e.file_name(), e.line_number());
};

void init() {
  printf("Initializing runtime\n");

  etl::error_handler::set_callback<printError>();

  for (kmp_int32 i = 0; i < NUM_CORES; i++) {
    threads.emplace_back(i);
  }
};

void runThread(kmp_int32 core_id) { threads[core_id].run(); };

Thread &getCurrentThread() { return threads[mempool_get_core_id()]; };

} // namespace runtime

} // namespace kmp
