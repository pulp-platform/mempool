#include <stdint.h>

struct __kmp_barrier_t {
  bool init = false;
  uint32_t barrier = 0;
};

void __kmp_barrier(volatile uint32_t *barrier, uint32_t num_cores);

void __kmp_barrier_init(volatile uint32_t *barrier, uint32_t core_id, uint32_t root);
