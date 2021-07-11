#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

void GOMP_sections_end_nowait()
{
    // printf("e%d\n",omp_get_thread_num());
}


int GOMP_sections_next()
{
    
    int chunk, left, start, end;
    
    

    uint32_t islocked = 1;

    while(islocked){
      islocked = __atomic_fetch_or(&works.lock, 1, __ATOMIC_SEQ_CST);
    }
    
    
    start = works.next;
    if (start == works.end)
    {
        __atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);
        // printf("n%d\n",0);
        return 0;
    }
    
    chunk = works.chunk_size * works.incr;
    
    left = works.end - start;

    if (chunk > left)
        chunk = left;

    end = start + chunk;
    
    works.next = end;

    __atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);
    
    // printf("n%d\n",start);
    return start;
}

/*
 #pragma omp parallel for sections
*/
void GOMP_parallel_sections (void (*fn) (void *), void *data, unsigned int num_threads, int count)
{
    // printf("GOMP_parallel_sections\n");
    uint32_t core_id = mempool_get_core_id();
    works.end = count + 1;
    works.next = 1;
    works.chunk_size = 1;
    works.incr = 1;
    works.lock = 0;

    GOMP_parallel_start(fn, data, num_threads);
    run_task(core_id);
    GOMP_parallel_end();

}

extern void GOMP_sections_end()
{
    
}

/*
TODO
 #pragma omp parallel 
 code
    #pragma omp sections
*/
// int GOMP_sections_start (int count)
// {
//     int ret = 0;
//     works.end = count + 1;
//     works.next = 1;
//     works.chunk_size = 1;
//     works.incr = 1;

//     works.lock = 0;

//     uint32_t islocked = 1;

//     while(islocked){
//       islocked = __atomic_fetch_or(&works.lock, 1, __ATOMIC_SEQ_CST);
//     }
    
//     if (works.next != works.end)
//         ret = works.next++;
    
//     __atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);

//     // printf("s%d\n",ret);
//     return ret;
// }

