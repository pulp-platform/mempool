#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "libgomp.h"

#define REPETITIONS 10 /* Number of times to run each test */
#define SLEEPTIME 1000

uint32_t * lock;
uint32_t result;
extern uint32_t barrier_init;

void work1(){
  int sum=0;
  for(int i=0; i<100; i++){
    sum++;
  }
}

parallel_critical_manual()
{
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t islocked = 1;
  
  work1();

  mempool_timer_t cycles = mempool_get_timer();
  mempool_start_benchmark();

  while(islocked){
    islocked = __atomic_fetch_or(lock, 1, __ATOMIC_SEQ_CST);
  }

  result += 100;

  __atomic_fetch_and(lock, 0, __ATOMIC_SEQ_CST);

  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;

  mempool_barrier(num_cores, num_cores * 4);

  if(core_id==0){
    printf("Manual Critical Result: %d\n", result);
    printf("Manual Critical Duration: %d\n", cycles);
  }
}

omp_parallel_critical()
{
  uint32_t core_id;
  uint32_t num_cores = mempool_get_core_count();

  #pragma omp parallel num_threads(num_cores)
  {
    work1();

    mempool_timer_t cycles = mempool_get_timer();
    mempool_start_benchmark();

    #pragma omp critical
    {
      result += 100;
    }

    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;

    mempool_barrier(num_cores, num_cores * 4);

    #pragma omp master
    {
    printf("OMP Critical Result: %d\n", result);
    printf("OMP Critical Duration: %d\n", cycles);
    }
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id, num_cores);

  // #ifdef VERBOSE
  if (core_id == 0) {
    printf("Initialize\n");
    *lock = 0;
    result = 0;
  }
  
  mempool_barrier(num_cores, num_cores * 4);
  parallel_critical_manual();
  mempool_barrier(num_cores, num_cores * 4);

  result = 0;

/*  OPENMP IMPLEMENTATION  */

  if(core_id == 0){
    mempool_wait(4*num_cores);
    omp_parallel_critical();
    mempool_wait(4*num_cores);
  }
  else{
    while(1){
      mempool_wfi();
      run_task(core_id);
    }
  }
  return 0;
}
