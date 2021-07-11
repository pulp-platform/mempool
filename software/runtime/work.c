#include "libgomp.h"
#include "runtime.h"
#include "printf.h"
#include "encoding.h"
#include "synchronization.h"

void gomp_new_work_share()
{
    works.lock = 0;
    works.checkfirst = WS_NOT_INITED;
    works.completed = 0;
    works.critical_lock = 0;
    works.atomic_lock = 0;
}

int gomp_work_share_start(void)
{
    int ret = 0;
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

    return ret;
}

