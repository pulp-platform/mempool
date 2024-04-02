#include "runtime.h"
#include <stdint.h>

void __kmp_barrier(volatile uint32_t *barrier, uint32_t num_cores) {
  // Increment the barrier counter
  if ((num_cores - 1) == __atomic_fetch_add(barrier, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(barrier, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
  }
  // Some threads have not reached the barrier --> Let's wait
  // Clear the wake-up trigger for the last core reaching the barrier as well
  mempool_wfi();
}

void __kmp_barrier_init(volatile uint32_t *barrier, uint32_t core_id,
                        uint32_t root) {
  if (core_id == root) {
    // Initialize the barrier
    barrier = 0;
    wake_up_all();
    mempool_wfi();
  } else {
    mempool_wfi();
  }
}
