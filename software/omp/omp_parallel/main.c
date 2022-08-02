#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

int main() {
  uint32_t core_id = mempool_get_core_id();

  mempool_barrier_init(core_id);

  if (core_id == 0) {
    printf("Master Thread: Parallel start\n");
    mempool_wait(1000);
#pragma omp parallel num_threads(8)
    { printf("%d\n", omp_get_num_threads()); }
    printf("Master Thread: Parallel end\n\n\n");

    printf("Master Thread: Parallel start\n");
    mempool_wait(1000);
#pragma omp parallel
    { printf("%d\n", omp_get_num_threads()); }
    printf("Master Thread: Parallel end\n\n\n");
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
