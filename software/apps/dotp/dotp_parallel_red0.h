#include <stdint.h>
#include <string.h>
#include "math.h"

/*******************************************************/
/**                    MULTI-CORE                     **/
/*******************************************************/


/* Parallel dot-product */
void dotp_parallel_red0  ( int32_t* in_a,
                           int32_t* in_b,
                           int32_t* s,
                           uint32_t N_vect,
                           uint32_t id) {

  /*uint32_t BlkSize = N_branch;
  if (id < ((N_vect%1024)/4)){
    BlkSize += 4;
  }
  else if (id == ((N_vect%1024)/4)) {
    BlkSize += N_vect%4;
  }

  uint32_t BlkCount = 0;
  uint32_t idxBank = ((id>>2)<<4) + (id%4)*4;
  uint32_t idx = idxBank;
  int32_t local_sum = 0;
  while (BlkCount<BlkSize) {
    //idx = idxBank + BlkCount%4;
    //idx += (BlkCount/4)*1024;
    local_sum += in_a[idx]*in_b[idx];
    idx++;
    BlkCount++;
    if (BlkCount%4==0){
      idx += 1020;
    }
  }*/

  uint32_t remainder = N_vect%4;
  int32_t local_sum = 0;

  uint32_t idx_start = id*4;
  uint32_t idx_stop = N_vect - remainder;
  uint32_t idx;
  for (idx = idx_start; idx < idx_stop; idx+= 1024){
    local_sum += in_a[idx]*in_b[idx];
    local_sum += in_a[idx+1]*in_b[idx+1];
    local_sum += in_a[idx+2]*in_b[idx+2];
    local_sum += in_a[idx+3]*in_b[idx+3];
  }
  if ( id == (N_vect%1024)/4 ) {
    while(idx < N_vect){
      local_sum += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  s[id] = local_sum;
  //__atomic_fetch_add(&s[id>>6], local_sum, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished

  if(id == 0) {
    for(uint32_t i=1; i<256; i++) {
      s[0] += s[i];
    }
  }
  mempool_barrier(NUM_CORES); // wait until all cores have finished
}

/* Parallel dot-product with loop unrolling */
void dotp_parallel_unrolled4_red0  (  int32_t* in_a,
                                      int32_t* in_b,
                                      int32_t* s,
                                      uint32_t N_vect,
                                      uint32_t id) {

  /*uint32_t BlkSize = N_branch;
  if (id < ((N_vect%1024)/4)){
    BlkSize += 4;
  }
  else if (id == ((N_vect%1024)/4)) {
    BlkSize += N_vect%4;
  }

  uint32_t BlkSize4 = ((N_branch>>1)<<1);
  uint32_t BlkCount = 0;
  uint32_t idxBank = ((id>>2)<<4) + (id%4)*4;
  uint32_t idx = idxBank;
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;
  int32_t local_sum_3 = 0;
  int32_t local_sum_4 = 0;
  while (BlkCount<BlkSize4) {
    int32_t in_a1 = in_a[idx];
    int32_t in_b1 = in_b[idx++];
    int32_t in_a2 = in_a[idx];
    int32_t in_b2 = in_b[idx++];
    int32_t in_a3 = in_a[idx];
    int32_t in_b3 = in_b[idx++];
    int32_t in_a4 = in_a[idx];
    int32_t in_b4 = in_b[idx++];
    local_sum_1 += in_a1*in_b1;
    local_sum_2 += in_a2*in_b2;
    local_sum_3 += in_a3*in_b3;
    local_sum_4 += in_a4*in_b4;
    BlkCount += 4;
    idx = idx + 1020;
  }
  while (BlkCount<BlkSize) {
    local_sum_1 += in_a[idx]*in_b[idx];
    idx++;
    BlkCount++;
    if (BlkCount%4==0){
      idx += 1020;
    }
  }
  local_sum_1 += local_sum_2;
  local_sum_3 += local_sum_4;
  local_sum_1 += local_sum_3;*/

  uint32_t const remainder = N_vect%4;
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;
  int32_t local_sum_3 = 0;
  int32_t local_sum_4 = 0;

  uint32_t idx_start = id*4;
  uint32_t idx_stop = N_vect - remainder;
  uint32_t idx;
  for (idx = idx_start; idx< idx_stop; idx+= 1024){
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
  }
  if (id == ((N_vect%1024)/4)) {
    while(idx<N_vect){
      local_sum_1 += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  local_sum_1 += local_sum_2;
  local_sum_3 += local_sum_4;
  local_sum_1 += local_sum_3;

  s[id] = local_sum_1;
  //__atomic_fetch_add(&s[id>>6], local_sum_1, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished

  if(id == 0) {
    for(uint32_t i=1; i<256; i++) {
      s[0] += s[i];
    }
  }
  mempool_barrier(NUM_CORES); // wait until all cores have finished
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
    s[k] = 0;
  }
}
