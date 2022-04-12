#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "dotp_single.h"
#include "dotp_parallel.h"
#include "dotp_parallel_red0.h"

#define N 1024
#define N_BRANCH (N/1024)*4
//#define SINGLE
#define PARALLEL
#define UNROLLED

// Vectors for kernel computation
int32_t vector_a[N] 										__attribute__((aligned(64*1024), section(".l1")));
int32_t vector_b[N] 										__attribute__((aligned(64*1024), section(".l1")));
int32_t sum                             __attribute__((section(".l1")));
//int32_t sum[4]                            __attribute__((section(".l1")));

// Vectors for performance metrics
uint32_t instr_init[NUM_CORES]			    __attribute__((section(".l1")));
uint32_t instr_end[NUM_CORES]	          __attribute__((section(".l1")));
uint32_t instrstalls_init[NUM_CORES]	  __attribute__((section(".l1")));
uint32_t instrstalls_end[NUM_CORES]	    __attribute__((section(".l1")));
uint32_t lsustalls_init[NUM_CORES]	    __attribute__((section(".l1")));
uint32_t lsustalls_end[NUM_CORES]	      __attribute__((section(".l1")));
uint32_t rawstalls_init[NUM_CORES]	    __attribute__((section(".l1")));
uint32_t rawstalls_end[NUM_CORES]	      __attribute__((section(".l1")));
int32_t result   												__attribute__((section(".l1")));
int32_t check              							__attribute__((section(".l1")));
int volatile error 											__attribute__((section(".l1")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t time_init, time_end;

  //initialize synchronization variables
  mempool_barrier_init(core_id);

  if (core_id == 0) {

  	error = 0;
  	time_init = 0;
  	time_end = 0;
    check = 0;

    init_vectors(	  vector_a, vector_b, &sum,
    								instr_init, instr_end,
    								instrstalls_init, instrstalls_end,
    								lsustalls_init, lsustalls_end,
    								rawstalls_init, rawstalls_end,
  									&result, &check, N);

    /*init_vectors_red0(   vector_a, vector_b, sum,
                    instr_init, instr_end,
                    instrstalls_init, instrstalls_end,
                    lsustalls_init, lsustalls_end,
                    rawstalls_init, rawstalls_end,
                    &result, &check, N);*/


  }
  mempool_barrier(NUM_CORES); // wait until all cores have finished

  // Kernel execution
  time_init = mempool_get_timer();
  mempool_start_benchmark();
  //asm volatile ("csrr %0, 0xb02" : "=r" (instr_init[core_id]));
  //asm volatile ("csrr %0, 0xb03" : "=r" (instrstalls_init[core_id]));
  //asm volatile ("csrr %0, 0xb04" : "=r" (lsustalls_init[core_id]));
  //asm volatile ("csrr %0, 0xb05" : "=r" (rawstalls_init[core_id]));
  instr_init[core_id] 				= read_csr(minstret);
  instrstalls_init[core_id] 	= read_csr(mhpmcounter3);
  lsustalls_init[core_id] 		= read_csr(mhpmcounter4);
  rawstalls_init[core_id] 		= read_csr(mhpmcounter5);

  #ifdef SINGLE

    #ifdef UNROLLED
      dotp_single_unrolled4(vector_a, vector_b, &sum, N, core_id);
    #else
      dotp_single(vector_a, vector_b, &sum, N, core_id);
    #endif

  #endif

  #ifdef PARALLEL

  	#ifdef UNROLLED
      dotp_parallel_unrolled4(vector_a, vector_b, &sum, N, core_id);
  		//dotp_parallel_unrolled4_red0(vector_a, vector_b, sum, N, N_BRANCH, core_id);
  	#else
      dotp_parallel(vector_a, vector_b, &sum, N, core_id);
  		//dotp_parallel_red0(vector_a, vector_b, sum, N, N_BRANCH, core_id);
  	#endif

  #endif

  //asm volatile ("csrr %0, 0xb04" : "=r" (lsustalls_end[core_id]));
  //asm volatile ("csrr %0, 0xb05" : "=r" (rawstalls_end[core_id]));
  //asm volatile ("csrr %0, 0xb03" : "=r" (instrstalls_end[core_id]));
  //asm volatile ("csrr %0, 0xb02" : "=r" (instr_end[core_id]));
  rawstalls_end[core_id]    = read_csr(mhpmcounter5);
  lsustalls_end[core_id] 		= read_csr(mhpmcounter4);
  instrstalls_end[core_id]  = read_csr(mhpmcounter3);
  instr_end[core_id]        = read_csr(minstret);
  mempool_stop_benchmark();
  time_end = mempool_get_timer();


  // Check results
  if (core_id == 0) {

  	#ifdef PARALLEL


			uint32_t mean_instrstalls = 0;
			uint32_t mean_lsustalls = 0;
			uint32_t mean_rawstalls = 0;
			uint32_t mean_instr = 0;
			for(uint32_t k=0; k < NUM_CORES; k++) {

		  		//printf("Core nb. %d says: \"I got %d instruction stalls :( ...\"\n", k, instrstalls_end[k]-instrstalls_init[k]);
					mean_instr       += (instr_end[k]-instr_init[k]);
		  		mean_instrstalls += (instrstalls_end[k]-instrstalls_init[k]);
		  	  mean_lsustalls   += (lsustalls_end[k]-lsustalls_init[k]);
		  		mean_rawstalls   += (rawstalls_end[k]-rawstalls_init[k]);

			}

      //result = sum[0];
      result = sum;
      uint32_t clock_cycles = (time_end-time_init);
			printf("Result ==> %d\n", result);
			printf("Check  ==> %d\n\n", check);
			printf("******** Performance-metrics *********\n");
      printf("\nKernel execution takes %d clock cycles\n", clock_cycles);
			printf("Total instructions: %d\n", mean_instr);
			printf("Mean instructions: %d\n", mean_instr/NUM_CORES);
			printf("Mean instruction stalls: %d\n", mean_instrstalls/NUM_CORES);
			printf("Mean load-store stalls: %d\n", mean_lsustalls/NUM_CORES);
			printf("Mean read-after-write stalls: %d\n", mean_rawstalls/NUM_CORES);

		#else

			result = sum;
	  	uint32_t clock_cycles = (time_end-time_init);
			printf("Result ==> %d\n", result);
			printf("Check  ==> %d\n\n", check);
		  printf("******* Performance-metrics ********\n");
      printf("\nKernel execution takes %d clock cycles\n", clock_cycles);
			printf("Instructions: %d\n", (instr_end[0]-instr_init[0]));
			printf("Instruction stalls: %d\n", (instrstalls_end[0]-instrstalls_init[0]));
			printf("Load-store stalls: %d\n", (lsustalls_end[0]-lsustalls_init[0]));
			printf("Read-after-write stalls: %d\n", (rawstalls_end[0]-rawstalls_init[0]));

		#endif
  }
  mempool_barrier(NUM_CORES); // wait until all cores have finished

  return error;

}
