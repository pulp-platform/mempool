#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"


void GOMP_barrier(){
    // printf("GOMP barrier\n");
    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = event.nthreads;
    // printf("core ID: %d\n",core_id);
    // printf("num cores: %d\n",num_cores);
    mempool_barrier_gomp(core_id, num_cores);
}

