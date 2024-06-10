// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This file handles the SINGLE construct.  */

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

/* This routine is called when first encountering a SINGLE construct that
   doesn't have a COPYPRIVATE clause.  Returns true if this is the thread
   that should execute the clause.  */

int GOMP_single_start(void) {
  int ret = 0;

  // NOTE works return from this function already locked
  ret = gomp_work_share_start();

  __atomic_add_fetch(&works.completed, 1, __ATOMIC_SEQ_CST);

  if (works.completed == event.nthreads) {
    works.checkfirst = WS_NOT_INITED;
  }

  gomp_hal_unlock(&works.lock);

  return ret;
}

/* This routine is called when first encountering a SINGLE construct that
   does have a COPYPRIVATE clause.  Returns NULL if this is the thread
   that should execute the clause; otherwise the return value is pointer
   given to GOMP_single_copy_end by the thread that did execute the clause.  */

void *GOMP_single_copy_start(void) {
  uint32_t core_id = mempool_get_core_id();

  void *ret;
  gomp_hal_lock(&works.lock);

  if (works.checkfirst != WS_INITED) {
    /* This section is performed only by first thread of next new_ws*/
    works.checkfirst = WS_INITED;

    works.completed = 0;
    ret = NULL;

    __atomic_add_fetch(&works.completed, 1, __ATOMIC_SEQ_CST);
    gomp_hal_unlock(&works.lock);
  } else {
    uint32_t completed =
        __atomic_add_fetch(&works.completed, 1, __ATOMIC_SEQ_CST);
    gomp_hal_unlock(&works.lock);

    mempool_barrier_gomp(core_id, event.nthreads);
    if (completed == event.nthreads) {
      works.checkfirst = WS_NOT_INITED;
    }
    ret = works.copyprivate;
  }
  return ret;
}

/* This routine is called when the thread that entered a SINGLE construct
   with a COPYPRIVATE clause gets to the end of the construct.  */

void GOMP_single_copy_end(void *data) {
  uint32_t core_id = mempool_get_core_id();
  works.copyprivate = data;
  mempool_barrier_gomp(core_id, event.nthreads);
}
