#include "etl/vector.h"
#include "kmp/types.h"
#include "kmp/thread.hpp"
#include "printf.h"

namespace kmp {

namespace runtime {

etl::vector<kmp::Thread, NUM_CORES> threads(NUM_CORES);

void printError(const etl::exception &e) {
  printf("%s %s %d\n", e.what(), e.file_name(), e.line_number());
};

void init() {
  printf("Initializing runtime\n");

  etl::error_handler::set_callback<printError>();

  for (kmp_int32 i = 0; i < NUM_CORES; i++) {
    threads[i].coreId = i;
  }
};

void runThread(kmp_int32 core_id) { threads[core_id].run(); };

} // namespace runtime



} // namespace kmp
