#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

void work(int num) {
  int i;
  volatile int cnt = 0;

  for (i = 0; i < num; i++) {
    cnt += i;
  }
}

void gcc_omp_parallel_for_schedule_dynamic(void) {
  int buf[64];
  int i, j;
  int result = 0;
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 10; j < 54; j++)
    buf[j] = 5;
  for (i = 0; i < 64; i++)
    if (buf[i] != 5 * (i >= 10 && i < 54)) {
      printf("error 1 at gcc schedule dynamic\n");
      result += 1;
    }
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 3; j <= 63; j += 2)
    buf[j - 2] = 6;
  for (i = 0; i < 64; i++)
    if (buf[i] != 6 * ((i & 1) && i <= 61)) {
      printf("error 2 at gcc schedule dynamic\n");
      result += 1;
    }
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 16; j < 51; j += 4)
    buf[j + 2] = 7;
  for (i = 0; i < 64; i++)
    if (buf[i] != 7 * ((i & 3) == 2 && i >= 18 && i < 53)) {
      printf("error 3 at gcc schedule dynamic\n");
      result += 1;
    }
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 16; j <= 40; j += 4)
    buf[j + 2] = -7;
  for (i = 0; i < 64; i++)
    if (buf[i] != -7 * ((i & 3) == 2 && i >= 18 && i <= 42)) {
      printf("error 4 at gcc schedule dynamic\n");
      result += 1;
    }
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 53; j > 9; --j)
    buf[j] = 5;
  for (i = 0; i < 64; i++)
    if (buf[i] != 5 * (i >= 10 && i < 54)) {
      printf("error 5 at gcc schedule dynamic\n");
      result += 1;
    }
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 63; j >= 3; j -= 2)
    buf[j - 2] = 6;
  for (i = 0; i < 64; i++)
    if (buf[i] != 6 * ((i & 1) && i <= 61)) {
      printf("error 6 at gcc schedule dynamic\n");
      result += 1;
    }
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 48; j > 15; j -= 4)
    buf[j + 2] = 7;
  for (i = 0; i < 64; i++)
    if (buf[i] != 7 * ((i & 3) == 2 && i >= 18 && i < 53)) {
      printf("error 7 at gcc schedule dynamic\n");
      result += 1;
    }
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 40; j >= 16; j -= 4)
    buf[j + 2] = -7;
  for (i = 0; i < 64; i++)
    if (buf[i] != -7 * ((i & 3) == 2 && i >= 18 && i <= 42)) {
      printf("error 8 at gcc schedule dynamic\n");
      result += 1;
    }
  if (result == 0) {
    printf("All tests passed\n");
  } else {
    printf("Failed %d tests", result);
  }
}

// void gcc_omp_parallel_for_schedule_dynamic_thread_test(void){
//     printf("Testing: schedule chunk size 1\n");
//     #pragma omp parallel for num_threads(4) schedule(dynamic)
//     for (int k = 0; k < 10; k++){
//       printf("%d\n", omp_get_thread_num());
//     }

//     printf("Testing: schedule chunk size 2\n");
//     #pragma omp parallel for num_threads(4) schedule(dynamic,3)
//     for (int k = 0; k < 10; k++){
//         printf("%d\n", omp_get_thread_num());
//     }
// }

int main() {
  uint32_t core_id = mempool_get_core_id();

  mempool_barrier_init(core_id);

  if (core_id == 0) {

    mempool_wait(1000);

    ///////////////////////////////////////////////////////////
    //////////////////////   test   ///////////////////////////
    ///////////////////////////////////////////////////////////

    gcc_omp_parallel_for_schedule_dynamic();

    ///////////////////////////////////////////////////////////
    /////////////////////   Benchmark   ///////////////////////
    ///////////////////////////////////////////////////////////
    // uint32_t time;
    // mempool_start_benchmark();
    // #pragma omp parallel for num_threads(2) schedule(dynamic,2)
    // for(int i = 0; i < 6400; i++){
    //   work(10);
    // }
    // mempool_stop_benchmark();
    // time = mempool_get_timer();
    // printf("Parallel Time %d\n",time);

    // mempool_start_benchmark();
    // for(int i = 0; i < 6400; i++){
    //   work(10);
    // }
    // mempool_stop_benchmark();
    // time = mempool_get_timer();
    // printf("Sequential Time %d\n",time);

  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
