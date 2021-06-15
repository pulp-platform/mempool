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


void work(int num)
{
  int i;
  volatile int cnt = 0;

  for(i = 0; i < num; i++)
  {
      cnt += i;
  }   
}


int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t time;

  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    printf("Parallel start\n");
    mempool_wait(1000);
    

    mempool_start_benchmark(); 
    #pragma omp parallel for num_threads(16) schedule(dynamic,10)
    for(int i = 0; i < 160; i++){
      work(100);
    }
    mempool_stop_benchmark();
    time = mempool_get_timer();
    printf("Parallel Time %d\n",time);
    printf("Parallel end \n\n\n");

    mempool_start_benchmark();
    for(int i = 0; i < 160; i++){
      work(100);
    }
    mempool_stop_benchmark();
    time = mempool_get_timer();
    printf("Sequential Time %d\n",time);

  } 
  else {
    while(1){
      mempool_wfi();
      run_task(core_id);
    }
  }
  // mempool_barrier(num_cores, num_cores * 4);

  return 0;
}




