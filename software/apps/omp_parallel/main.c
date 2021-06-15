#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "libgomp.h"
#include "synchronization.h"

volatile uint32_t atomic __attribute__((section(".l2"))) = (uint32_t)-1;

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    printf("Master Thread: Parallel start\n");
    mempool_wait(1000);
    #pragma omp parallel num_threads(8)
    {
      printf("A\n");
    }
    printf("Master Thread: Parallel end\n\n\n");

    printf("Master Thread: Parallel start\n");
    mempool_wait(1000);
    #pragma omp parallel 
    {
      printf("B\n");
    }
    printf("Master Thread: Parallel end\n\n\n");
  } else {
    while(1){
      mempool_wfi();
      run_task(core_id);
    }
  }
  // mempool_barrier(num_cores, num_cores * 4);

  return 0;
}
