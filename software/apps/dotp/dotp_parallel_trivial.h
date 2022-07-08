#include <stdint.h>
#include <string.h>
#include "math.h"
#include "define.h"

/* Parallel dot-product */
void dotp_parallel_trivial (	int32_t* in_a,
                  						int32_t* in_b,
                  						int32_t* s,
                  						uint32_t Len,
                              uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  int32_t local_sum = 0;
	for(uint32_t i = core_id*step; i < core_id*step+step; i++) {
		local_sum += in_a[i]*in_b[i];
  }
  mempool_stop_benchmark();
  mempool_start_benchmark();
  __atomic_fetch_add(s, local_sum, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES);
}
