/* This file handles the SECTIONS construct.  */

#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"



void
gomp_sections_init(int count)
{
  works.end = count + 1;
  works.next = 1;
  works.chunk_size = 1;
  works.incr = 1;
}

/*********************** APIs *****************************/

void GOMP_sections_end_nowait()
{

}


int GOMP_sections_next()
{
    int chunk, left, start, end;
    
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

    gomp_hal_unlock(&works.lock);
    
    return start;
}

/*
 #pragma omp parallel for sections
*/
void GOMP_parallel_sections (void (*fn) (void *), void *data, unsigned int num_threads, int count)
{
    // printf("GOMP_parallel_sections\n");
    uint32_t core_id = mempool_get_core_id();

    gomp_new_work_share();

    works.end = count + 1;
    works.next = 1;
    works.chunk_size = 1;
    works.incr = 1;

    GOMP_parallel_start(fn, data, num_threads);
    run_task(core_id);
    GOMP_parallel_end();

}

extern void GOMP_sections_end()
{
    
}

/*
 #pragma omp parallel 
 code
    #pragma omp sections
*/
int GOMP_sections_start (int count)
{
    int ret = 0;
    
    if (gomp_work_share_start()){ // work returns locked
      gomp_sections_init(count);
    }  
    
    if (works.next != works.end)
        ret = works.next++;
    
    gomp_hal_unlock(&works.lock);

    return ret;
}

