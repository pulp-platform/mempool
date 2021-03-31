#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

volatile uint32_t atomic __attribute__((section(".l2"))) = (uint32_t)-1;

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    // Do a lot of work
    mempool_wait(1000);
    wake_up(core_id + 1);
  } else {
    mempool_wfi();
    printf("Core %d woke up\n", core_id);
    wake_up(core_id + 1);
  }
  mempool_barrier(num_cores, num_cores * 4);

  return 0;
}
