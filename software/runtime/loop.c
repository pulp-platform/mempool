#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

void
gomp_loop_init(int start, int end, int incr, int chunk_size)
{
  works.chunk_size = chunk_size;
  works.end = end;
  works.incr = incr;
  works.next = start;
}

/*********************** APIs *****************************/

int
GOMP_loop_dynamic_start(int start, int end, int incr, int chunk_size,
                        int *istart, int *iend)
{
    int chunk, left;
    int ret = 1;
    
    if (gomp_work_share_start()){ // work returns locked
      gomp_loop_init(start, end, incr, chunk_size);
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
    
    gomp_hal_unlock(&works.lock);
    
    return ret;
}

int
GOMP_loop_dynamic_next (int *istart, int *iend)
{
    // printf("n\n");
    int start, end, chunk, left;

    gomp_hal_lock(&works.lock);
    
    start = works.next;
    if (start == works.end)
    {
        gomp_hal_unlock(&works.lock);
        return 0;
    }
    
    chunk = works.chunk_size * works.incr;
    
    left = works.end - start;

    if (chunk > left)
        chunk = left;

    end = start + chunk;
    
    works.next = end;
    // printf("%d %d \n", works.lock, end);

    gomp_hal_unlock(&works.lock);
    
    *istart = start;
    *iend = end;
    
    return 1;
}

void
GOMP_parallel_loop_dynamic (void (*fn) (void *), void *data,
                            unsigned num_threads, long start, long end,
                            long incr, long chunk_size)
{
    // printf("GOMP_parallel_loop_dynamic %d %d %d %d \n", start, end, incr, chunk_size);
    uint32_t core_id = mempool_get_core_id();

    gomp_new_work_share();
    gomp_loop_init(start, end, incr, chunk_size);

    GOMP_parallel_start(fn, data, num_threads);
    run_task(core_id);
    GOMP_parallel_end();
}

void
GOMP_loop_end()
{
  uint32_t core_id = mempool_get_core_id();
  mempool_barrier_gomp(core_id, event.nthreads);
}

void
GOMP_loop_end_nowait()
{
}
