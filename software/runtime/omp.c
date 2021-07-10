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
  // int* dd = (int*) data;
  // printf("task %d %d %d %d %d %d \n", *dd, *(dd+1), *(dd+2), *(dd+3), *(dd+4), *(dd+5));
  // printf("task %d %d %d %d %d %d \n", dd, (dd+1), (dd+2), (dd+3), (dd+4), (dd+5));
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
        // printf("r\n");
        event.fn(event.data);
        // printf("t\n");
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

void GOMP_parallel (void (*fn) (void*), void *data, unsigned int num_threads, unsigned int flags)
{
  // printf("GOMP_parallel\n");
  uint32_t core_id = mempool_get_core_id();

  works.checkfirst = WS_NOT_INITED;
  works.completed = 0;
  works.lock = 0;
  works.critical_lock = 0;
  works.atomic_lock = 0;
  
  GOMP_parallel_start(fn, data, num_threads);
  run_task(core_id);
  GOMP_parallel_end();
}


void GOMP_parallel_loop_dynamic (void (*fn) (void *), void *data, unsigned num_threads, long start, long end, long incr, long chunk_size)
{

    printf("GOMP_parallel_loop_dynamic %d %d %d %d \n", start, end, incr, chunk_size);
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

void GOMP_loop_end()
{
}

int GOMP_loop_dynamic_next (int *istart, int *iend)
{

    // printf("n\n");
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


int GOMP_loop_dynamic_start(int start, int end, int incr, int chunk_size, int *istart, int *iend)
{
    
    int chunk, left;
    int ret = 1;
    
    if (gomp_work_share_start()){
      works.chunk_size = chunk_size;
      works.end = end;
      works.incr = incr;
      works.next = start;
      // printf("GOMP_parallel_loop_dynamic_start %d %d %d %d \n", start, end, incr, chunk_size);
    }  
    
    start = works.next;
    
    if (start == works.end)
        ret = 0;
    
    if(ret)
    {
        chunk = chunk_size * incr;
        
        left = works.end - start;
        
        if (chunk > left){
            chunk = left;
        }
        

        end = start + chunk;
        works.next = end;
    }
    
    *istart = start;
    *iend   = end;
    
    __atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);
    
    return ret;
}





int gomp_work_share_start(void)
{
    int ret = 0;
    // printf("SINGLE START\n");
    uint32_t islocked = 1;

    while(islocked){
      islocked = __atomic_fetch_or(&works.lock, 1, __ATOMIC_SEQ_CST);
    }
    
    if (works.checkfirst != WS_INITED)
    {
        /* This section is performed only by first thread of next new_ws*/
        works.checkfirst = WS_INITED;
        ret = 1;
    }

    return ret;
}



uint32_t omp_get_num_threads(void){
    // printf("a\n");
  return event.nthreads;
}

uint32_t omp_get_thread_num(void){
    // printf("b\n");
  return mempool_get_core_id();
}


