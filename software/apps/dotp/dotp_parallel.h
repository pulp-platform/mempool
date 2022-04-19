#include <stdint.h>
#include <string.h>
#include "math.h"

#define N_BANK NUM_CORES*4

/*******************************************************/
/**                    MULTI-CORE                     **/
/*******************************************************/


/* Parallel dot-product */
void dotp_parallel  ( int32_t* in_a,
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
  }
  __atomic_fetch_add(&s[0], local_sum, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished*/

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
  __atomic_fetch_add(&s[0], local_sum, __ATOMIC_RELAXED);
  mempool_stop_benchmark();
  mempool_start_benchmark();
  mempool_barrier(NUM_CORES); // wait until all cores have finished
}


/* Parallel dot-product with loop unrolling */
void dotp_parallel_unrolled2 ( int32_t* in_a,
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
  uint32_t BlkSize2 = ((N_branch>>1)<<1);

  uint32_t BlkCount = 0;
  uint32_t idxBank = ((id>>2)<<4) + (id%4)*4;
  uint32_t idx = idxBank;
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;
  while (BlkCount<BlkSize2) {

    int32_t in_a1 = in_a[idx++];
    int32_t in_a2 = in_a[idx++];
    int32_t in_b1 = in_b[idx++];
    int32_t in_b2 = in_b[idx++];
    local_sum_1 += in_a1*in_b1;
    local_sum_2 += in_a2*in_b2;
    BlkCount += 2;
    if (BlkCount%4==0){
      idx += 1020;
    }

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
  __atomic_fetch_add(&s[0], local_sum_1, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished*/

  uint32_t const remainder = N_vect%4;
  uint32_t const idx_stop = N_vect - remainder;
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;

  uint32_t idx = id*4;
  while (idx < idx_stop){
    int32_t in_a1 = in_a[idx];
    int32_t in_b1 = in_b[idx];
    int32_t in_a2 = in_a[idx+1];
    int32_t in_b2 = in_b[idx+1];
    local_sum_1 += in_a1*in_b1;
    local_sum_2 += in_a2*in_b2;
    in_a1 = in_a[idx+2];
    in_b1 = in_b[idx+2];
    in_a2 = in_a[idx+3];
    in_b2 = in_b[idx+3];
    local_sum_1 += in_a1*in_b1;
    local_sum_2 += in_a2*in_b2;
    idx += N_BANK;
  }
  if (id == ((N_vect%N_BANK)/4)) {
    while(idx<N_vect){
      local_sum_1 += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  local_sum_1 += local_sum_2;
  __atomic_fetch_add(&s[0], local_sum_1, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished

}

/* Parallel dot-product with loop unrolling */
void dotp_parallel_unrolled4  ( int32_t* in_a,
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
  uint32_t BlkSize4 = ((N_branch>>2)<<2);

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
  local_sum_1 += local_sum_3;
  __atomic_fetch_add(&s[0], local_sum_1, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished*/

  uint32_t const remainder = N_vect%4;
  uint32_t const idx_stop = N_vect - remainder;
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;
  int32_t local_sum_3 = 0;
  int32_t local_sum_4 = 0;

  uint32_t idx = id*4;
  while (idx < idx_stop){
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
    while(idx < N_vect){
      local_sum_1 += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  local_sum_1 += local_sum_2;
  local_sum_3 += local_sum_4;
  local_sum_1 += local_sum_3;
  __atomic_fetch_add(&s[0], local_sum_1, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES); // wait until all cores have finished

}
