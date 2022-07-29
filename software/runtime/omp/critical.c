/* This file handles the ATOMIC and CRITICAL constructs.  */

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

void GOMP_atomic_start() {
  // printf("GOMP_critical_start %d\n",mempool_get_core_id());

  gomp_hal_lock(&works.atomic_lock);
}

void GOMP_atomic_end() {
  // printf("GOMP_critical_end %d\n",mempool_get_core_id());

  gomp_hal_unlock(&works.atomic_lock);
}

void GOMP_critical_start() {
  // printf("GOMP_critical_start %d\n",mempool_get_core_id());

  gomp_hal_lock(&works.critical_lock);
}

void GOMP_critical_end() {
  // printf("GOMP_critical_end %d\n",mempool_get_core_id());

  gomp_hal_unlock(&works.critical_lock);
}
