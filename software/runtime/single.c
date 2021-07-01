#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

/* This routine is called when first encountering a SINGLE construct that
   doesn't have a COPYPRIVATE clause.  Returns true if this is the thread
   that should execute the clause.  */

int GOMP_single_start(void)
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

        works.completed = 0;
        ret = 1;
    }
    
    __atomic_add_fetch(&works.completed, 1, __ATOMIC_SEQ_CST);

    if (works.completed == event.nthreads)
    {
        works.checkfirst = WS_NOT_INITED;
        
    }

    __atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);

    return ret;
}

/* This routine is called when first encountering a SINGLE construct that
   does have a COPYPRIVATE clause.  Returns NULL if this is the thread
   that should execute the clause; otherwise the return value is pointer
   given to GOMP_single_copy_end by the thread that did execute the clause.  */

void * GOMP_single_copy_start (void){
    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();

    void *ret;
    //printf("SINGLE COPY START\n");
    uint32_t islocked = 1;

    while(islocked){
      islocked = __atomic_fetch_or(&works.lock, 1, __ATOMIC_SEQ_CST);
    }
    
    if (works.checkfirst != WS_INITED)
    {
        /* This section is performed only by first thread of next new_ws*/
        works.checkfirst = WS_INITED;

        works.completed = 0;
        ret = NULL;
    
    	__atomic_add_fetch(&works.completed, 1, __ATOMIC_SEQ_CST);
    	__atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);
	}
	else
	{
		uint32_t completed = __atomic_add_fetch(&works.completed, 1, __ATOMIC_SEQ_CST);
		__atomic_fetch_and(&works.lock, 0, __ATOMIC_SEQ_CST);

		//printf("wait at barrier\n");
		mempool_barrier_gomp(core_id, event.nthreads);
		if (completed == event.nthreads)
		{
			works.checkfirst = WS_NOT_INITED;
		}
		ret = works.copyprivate;
	}
  return ret;
}

/* This routine is called when the thread that entered a SINGLE construct
   with a COPYPRIVATE clause gets to the end of the construct.  */

void GOMP_single_copy_end (void *data){
    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();
	works.copyprivate = data;
	//printf("single result %d\n",(uint32_t*)data);
	mempool_barrier_gomp(core_id, event.nthreads);
}