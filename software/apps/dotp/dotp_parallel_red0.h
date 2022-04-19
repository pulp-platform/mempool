#include <stdint.h>
#include <string.h>
#include "math.h"

#define N_BANK NUM_CORES*4

/*******************************************************/
/**                    MULTI-CORE                     **/
/*******************************************************/


/* Parallel dot-product */
void dotp_parallel_red0  ( int32_t* in_a,
                           int32_t* in_b,
                           int32_t* s,
                           uint32_t N_vect,
                           uint32_t id,
                           uint32_t* my_barrier) {

  uint32_t const remainder = N_vect%4;
  uint32_t const idx_stop = N_vect - remainder;
  int32_t local_sum = 0;

  uint32_t idx = id*4;
  while (idx < idx_stop) {
    local_sum += in_a[idx]*in_b[idx];
    local_sum += in_a[idx+1]*in_b[idx+1];
    local_sum += in_a[idx+2]*in_b[idx+2];

    local_sum += in_a[idx+3]*in_b[idx+3];
    idx+= N_BANK;
  }
  if ( id == (N_vect%N_BANK)/4 ) {
    while(idx < N_vect){
      local_sum += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  __atomic_fetch_add(&s[(id/4)*16], local_sum, __ATOMIC_RELAXED);
  //mempool_barrier(NUM_CORES); // wait until all cores have finished
  mempool_stop_benchmark();

  mempool_start_benchmark();
  if ((NUM_CORES - 1) == __atomic_fetch_add(my_barrier, 1, __ATOMIC_RELAXED)) {
    //__atomic_store_n(my_barrier, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    uint32_t idx_red = 0;
    local_sum = 0;
    while(idx_red < N_BANK) {
//      int32_t red_1 = s[idx_red];
//      int32_t red_2 = s[idx_red+16];
//      int32_t red_3 = s[idx_red+32];
//      int32_t red_4 = s[idx_red+48];
//      local_sum += red_1;
//      local_sum += red_2;
//      local_sum += red_3;
//      local_sum += red_4;
      local_sum += s[idx_red];
      idx_red += 16;
    }
    s[0] = local_sum;
    my_barrier = 0;
    wake_up_all();
  }
  mempool_wfi();

  /*if(id == 0) {
    uint32_t idx_red = 64;
    while(idx_red < N_BANK) {
      s[0] += s[idx_red];
      idx_red += 64;
    }
  }
  else {
    mempool_wait(5*N_BANK/64);
  }*/
  //mempool_barrier(NUM_CORES); // wait until all cores have finished

}

/* Parallel dot-product with loop unrolling */
void dotp_parallel_unrolled4_red0  (  int32_t* in_a,
                                      int32_t* in_b,
                                      int32_t* s,
                                      uint32_t N_vect,
                                      uint32_t id) {

  uint32_t const remainder = N_vect%4;
  uint32_t const idx_stop = N_vect - remainder;
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;
  int32_t local_sum_3 = 0;
  int32_t local_sum_4 = 0;

  uint32_t idx = id*4;
  while (idx< idx_stop) {
    int32_t in_a1 = in_a[idx];
    int32_t in_b1 = in_b[idx];
    int32_t in_a2 = in_a[idx+1];
    int32_t in_b2 = in_b[idx+1];
    int32_t in_a3 = in_a[idx+2];
    int32_t in_b3 = in_b[idx+2];
    int32_t in_a4 = in_a[idx+3];
    int32_t in_b4 = in_b[idx+3];
    local_sum_1 += in_a1*in_b1;
    local_sum_2 += in_a2*in_b2;
    local_sum_3 += in_a3*in_b3;
    local_sum_4 += in_a4*in_b4;
    idx+= N_BANK;
  }
  if (id == ((N_vect%N_BANK)/4)) {
    while(idx<N_vect){
      local_sum_1 += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  local_sum_1 += local_sum_2;
  local_sum_3 += local_sum_4;
  local_sum_1 += local_sum_3;

  //s[id] = local_sum_1;
  __atomic_fetch_add(&s[id>>6], local_sum_1, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished
  if(id == 0) {
    for(uint32_t i=1; i<NUM_CORES; i++) {
      s[0] += s[i];
    }
  }
  //mempool_barrier(NUM_CORES); // wait until all cores have finished
}

void init_vectors_red0(  int32_t* in_a, int32_t* in_b, int32_t* s,
          uint32_t* instr_init, uint32_t* instr_end,
          uint32_t* instrs_init, uint32_t* instrs_end,
          uint32_t* lsus_init, uint32_t* lsus_end,
          uint32_t* raws_init, uint32_t* raws_end,
          int32_t* p_result, int32_t* p_check, uint32_t N_vect) {
  *p_result = 0;
  *p_check = 0;

  for(uint32_t i = 0; i < N_vect; i++) {
    in_a[i] = (int32_t) i;
    in_b[i] = (int32_t) 1;
    *p_check = *p_check + (int32_t) i;
  }
  for(uint32_t k=0; k<NUM_CORES; k++) {
    instr_init[k] = 0;
    instr_end[k] = 0;
    instrs_init[k] = 0;
    instrs_end[k] = 0;
    lsus_init[k] = 0;
    lsus_end[k] = 0;
    raws_init[k] = 0;
    raws_end[k] = 0;
  }

  for(uint32_t k=0; k<N_BANK; k++) {
    s[k] = 0;
  }
}
