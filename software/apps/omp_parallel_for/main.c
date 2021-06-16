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


void work(unsigned long num)
{
  unsigned int i;
  volatile int cnt = 0;

  for(i=0; i<num; i++)
        cnt += i;
}

void gcc_omp_parallel_for_schedule_static (void)
{
  int buf[64], *p;
  int i;
  int result = 0;
  memset (buf, '\0', sizeof (buf));

#pragma omp parallel for
  for (i = 0; i < omp_get_num_threads(); i++){
    if(omp_get_thread_num()!=i){
      printf("Error: for loop is not executed in parallel\n");
      result += 1;
    }
  }

#pragma omp parallel for schedule (static, 3) private(p)
  for (p = &buf[10]; p < &buf[54]; p++)
    *p = 5;
  for (i = 0; i < 64; i++)
    if (buf[i] != 5 * (i >= 10 && i < 54)){
      printf("error 1 at gcc schedule static\n");
      result += 1;
    }
    
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[3]; p <= &buf[63]; p += 2)
    p[-2] = 6;
  for (i = 0; i < 64; i++)
    if (buf[i] != 6 * ((i & 1) && i <= 61)){
      printf("error 2 at gcc schedule static\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[16]; p < &buf[51]; p = 4 + p)
    p[2] = 7;
  for (i = 0; i < 64; i++)
    if (buf[i] != 7 * ((i & 3) == 2 && i >= 18 && i < 53)){
      printf("error 3 at gcc schedule static\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[16]; p <= &buf[40]; p = p + 4ULL)
    p[2] = -7;
  for (i = 0; i < 64; i++)
    if (buf[i] != -7 * ((i & 3) == 2 && i >= 18 && i <= 42)){
      printf("error 4 at gcc schedule static\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[53]; p > &buf[9]; --p)
    *p = 5;
  for (i = 0; i < 64; i++)
    if (buf[i] != 5 * (i >= 10 && i < 54)){
      printf("error 5 at gcc schedule static\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[63]; p >= &buf[3]; p -= 2)
    p[-2] = 6;
  for (i = 0; i < 64; i++)
    if (buf[i] != 6 * ((i & 1) && i <= 61)){
      printf("error 6 at gcc schedule static\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[48]; p > &buf[15]; p = -4 + p)
    p[2] = 7;
  for (i = 0; i < 64; i++)
    if (buf[i] != 7 * ((i & 3) == 2 && i >= 18 && i < 53)){
      printf("error 7 at at gcc schedule static\n");
      result += 1;
    }
  memset (buf, '\0', sizeof (buf));
#pragma omp parallel for schedule (static, 3)
  for (p = &buf[40]; p >= &buf[16]; p = p - 4ULL)
    p[2] = -7;
  for (i = 0; i < 64; i++)
    if (buf[i] != -7 * ((i & 3) == 2 && i >= 18 && i <= 42)){
      printf("error 8 at gcc schedule static\n");
      result += 1;
    }
  
  if(result == 0){
    printf("All test passed\n");
  }
  else{
    printf("Failed %d tests\n", result);
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t time;

  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    mempool_wait(1000);
    
  

    /////////////////////////////////////////////////////////// 
    //////////////////////   test   ///////////////////////////
    ///////////////////////////////////////////////////////////
    gcc_omp_parallel_for_schedule_static();

    printf("Testing: schedule default chunk size\n");
    #pragma omp parallel for num_threads(4) schedule(static)
    for (int i = 0; i < 10; i++){
      printf("%d\n", omp_get_thread_num());
    }

    printf("Testing: schedule chunk size 2\n");
    #pragma omp parallel for num_threads(4) schedule(static,2)
    for (int i = 0; i < 10; i++){
      printf("%d\n", omp_get_thread_num());
    }

    
    printf("Testing: private\n");
    int A = 9;
    #pragma omp parallel for num_threads(4) schedule(static) private(A)
    for (int i = 0; i < 4; i++){
      A = i;
      printf("%d\n", A);
    }
    printf("A %d\n", A);

    printf("Testing: First private\n");
    A = 9;
    #pragma omp parallel for num_threads(4) schedule(static) firstprivate(A)
    for (int i = 0; i < 4; i++){
      printf("%d\n", A);
      A = i;
      
    }
    printf("A %d\n", A);

    printf("Testing: Last private\n");
    A = 9;
    #pragma omp parallel for num_threads(4) schedule(static) lastprivate(A)
    for (int i = 0; i < 4; i++){
      A = i;
      
    }
    printf("A %d\n", A);


    

    /////////////////////////////////////////////////////////// 
    /////////////////////   Benchmark   ///////////////////////
    ///////////////////////////////////////////////////////////
    // mempool_start_benchmark();
    // #pragma omp parallel for num_threads(16) schedule(static,3)
    // for(int i = 0; i < 160; i++){
    //   work(10);
    // }
    // mempool_stop_benchmark();
    // time = mempool_get_timer();
    // printf("Parallel Time %d\n",time);

    // mempool_start_benchmark();
    // for(int i = 0; i < 160; i++){
    //   work(100);
    // }
    // mempool_stop_benchmark();
    // time = mempool_get_timer();
    // printf("Sequential Time %d\n",time);

  } 
  else {
    while(1){
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}




