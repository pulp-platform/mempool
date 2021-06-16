#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

// uint32_t volatile lock __attribute__((section(".l1"))) = 0;
// uint32_t volatile lock;
event_t event;
work_t works;

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
        event.fn(event.data);
        __atomic_add_fetch(&event.barrier, -1, __ATOMIC_SEQ_CST);
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
    	mempool_wait(4 * 16);
    }

}

void GOMP_parallel (void (*fn) (void*), void *data, unsigned int num_threads)
{
	// printf("GOMP_parallel\n");
	uint32_t core_id = mempool_get_core_id();

	GOMP_parallel_start(fn, data, num_threads);
	run_task(core_id);
	GOMP_parallel_end();
}

void GOMP_parallel_loop_dynamic (void (*fn) (void *), void *data, unsigned num_threads, long start, long end, long incr, long chunk_size)
{

    // printf("GOMP_parallel_loop_dynamic %d %d %d %d \n", start, end, incr, chunk_size);
    uint32_t core_id = mempool_get_core_id();
    works.chunk_size = chunk_size;
    works.end = end;
    works.incr = incr;
    works.next = start;
    works.lock = 0;



    GOMP_parallel_start(fn, data, num_threads);
    run_task(core_id);
    GOMP_parallel_end();
}

void GOMP_loop_end_nowait()
{
}

int GOMP_loop_dynamic_next (int *istart, int *iend)
{


    int start, end, chunk, left;
    uint32_t islocked = 1;

    while(islocked){
      islocked = __atomic_fetch_or(&works.lock, 1, __ATOMIC_SEQ_CST);
    }
    
    
    start = works.next;
    if (start == works.end)
    {
        __atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);
        return 0;
    }
    
    chunk = works.chunk_size * works.incr;
    
    left = works.end - start;

    if (chunk > left)
        chunk = left;

    end = start + chunk;
    
    works.next = end;
    // printf("%d %d \n", works.lock, end);

    __atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);
    
    *istart = start;
    *iend = end;
    
    return 1;
}












uint32_t omp_get_num_threads(void){
	return event.nthreads;
}

uint32_t omp_get_thread_num(void){
	return mempool_get_core_id();
}


