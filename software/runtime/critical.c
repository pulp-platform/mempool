#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

// implements atomic and critical constructs

void GOMP_critical_start(){
    // printf("GOMP_critical_start %d\n",mempool_get_core_id());

    uint32_t islocked = 1;

    while(islocked){
      islocked = __atomic_fetch_or(&works.critical_lock, 1, __ATOMIC_SEQ_CST);
    }
}

void GOMP_critical_end(){
    // printf("GOMP_critical_end %d\n",mempool_get_core_id());
    
    __atomic_fetch_and(&works.critical_lock, 0, __ATOMIC_SEQ_CST);
}


void GOMP_atomic_start(){
    // printf("GOMP_critical_start %d\n",mempool_get_core_id());

    uint32_t islocked = 1;

    while(islocked){
      islocked = __atomic_fetch_or(&works.atomic_lock, 1, __ATOMIC_SEQ_CST);
    }
}

void GOMP_atomic_end(){
    // printf("GOMP_critical_end %d\n",mempool_get_core_id());
    
    __atomic_fetch_and(&works.atomic_lock, 0, __ATOMIC_SEQ_CST);
}