#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"


event_t event;

void set_event(void (*fn) (void*), void *data, uint32_t nthreads)
{
  event.fn = fn;
  event.data = data;
  if(nthreads == 0){
    event.nthreads = 16;
    event.barrier = 16;
  }
  else{
    event.nthreads = nthreads;
    event.barrier = nthreads;
  }
  

  for(uint32_t i = 0; i < 16; i++)
  {
    event.thread_pool[i] = (i < event.nthreads) ? 1 : 0;
  }
}


void run_task(uint32_t core_id){
	
    if(event.thread_pool[core_id]){
        // printf(" %d\n", core_id);
        event.fn(event.data);
        __atomic_add_fetch(&event.barrier, -1, __ATOMIC_RELAXED);
    }
}

void GOMP_parallel_start (void (*fn) (void*), void *data, unsigned int num_threads)
{
	// printf("GOMP_parallel_start\n");
	set_event(fn, data, num_threads);
	wake_up((uint32_t)-1);
}

void GOMP_parallel_end (void)
{
    // printf("GOMP_parallel_end\n");

    while(event.barrier > 0){
    	// printf("  %d  \n", event.nthreads);
    	mempool_wait(4 * 16);
    }

}

void GOMP_parallel (void (*fn) (void*), void *data, unsigned int num_threads)
{
	// printf("GOMP_parallel num threads %d\n", num_threads);
	uint32_t core_id = mempool_get_core_id();

	GOMP_parallel_start(fn, data, num_threads);
	run_task(core_id);
	GOMP_parallel_end();
}

void GOMP_parallel_loop_dynamic (void (*fn) (void *), void *data, unsigned num_threads, long start, long end, long incr, long chunk_size, unsigned flags)
{

}

void GOMP_loop_end_nowait()
{

}

void GOMP_loop_dynamic_next (int *istart, int *iend)
{
    
}












uint32_t omp_get_num_threads(void){
	return event.nthreads;
}

uint32_t omp_get_thread_num(void){
	return mempool_get_core_id();
}


