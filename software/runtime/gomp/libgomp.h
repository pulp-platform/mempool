/* Copyright (C) 2005-2022 Free Software Foundation, Inc.
   Contributed by Richard Henderson <rth@redhat.com>.
   This file is part of the GNU Offloading and Multi Processing Library
   (libgomp).
   Libgomp is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.
   Libgomp is distributed in the hope that it will be useful, but WITHOUT ANY
   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
   more details.
   Under Section 7 of GPL version 3, you are granted additional
   permissions described in the GCC Runtime Library Exception, version
   3.1, as published by the Free Software Foundation.
   You should have received a copy of the GNU General Public License and
   a copy of the GCC Runtime Library Exception along with this program;
   see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
   <http://www.gnu.org/licenses/>.  */

/* This file contains data types and function declarations that are not
   part of the official OpenACC or OpenMP user interfaces.  There are
   declarations in here that are part of the GNU Offloading and Multi
   Processing ABI, in that the compiler is required to know about them
   and use them.
   The convention is that the all caps prefix "GOMP" is used group items
   that are part of the external ABI, and the lower case prefix "gomp"
   is used group items that are completely private to the library.  */

#ifndef __LIBGOMP_H__
#define __LIBGOMP_H__

#include "encoding.h"
#include "omp-lock.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define WS_INITED (0xfeeddeadU)
#define WS_NOT_INITED (0x0U)

/* barrier.c */
extern void GOMP_barrier(void);
extern void mempool_barrier_gomp(uint32_t, uint32_t);

/* critical.c */
extern void GOMP_atomic_start(void);
extern void GOMP_atomic_end(void);
extern void GOMP_critical_start(void);
extern void GOMP_critical_end(void);

/* loop.c */
extern int GOMP_loop_dynamic_start(int, int, int, int, int *, int *);
extern int GOMP_loop_dynamic_next(int *, int *);
extern void GOMP_parallel_loop_dynamic(void (*)(void *), void *, unsigned, long,
                                       long, long, long);
extern void GOMP_loop_end(void);
extern void GOMP_loop_end_nowait(void);

/* parallel.c */
extern void GOMP_parallel(void (*)(void *), void *, unsigned int, unsigned int);
extern void GOMP_parallel_start(void (*)(void *), void *, unsigned int);
extern void GOMP_parallel_end(void);

/* sections.c */
extern void GOMP_parallel_sections(void (*)(void *), void *, unsigned int, int);
extern int GOMP_sections_start(int);
extern void GOMP_sections_end(void);
extern void GOMP_sections_end_nowait(void);
extern int GOMP_sections_next(void);
extern void GOMP_parallel_sections_start(void (*)(void *), void *, unsigned,
                                         unsigned);

/* single.c */
extern int GOMP_single_start(void);
extern void *GOMP_single_copy_start(void);
extern void GOMP_single_copy_end(void *);

/* work.c */
extern void gomp_new_work_share(void);
extern int gomp_work_share_start(void);

/* parallel.c */
extern void set_event(void (*fn)(void *), void *data, uint32_t nthreads);
extern void run_task(uint32_t core_id);

typedef struct {
  void (*fn)(void *);
  void *data;
  uint32_t nthreads;
  uint32_t barrier;
  uint8_t thread_pool[NUM_CORES];
} event_t;

typedef struct {
  int end;
  int next;
  int chunk_size;
  int incr;

  omp_lock_t lock;

  // for single construct
  uint32_t checkfirst;
  uint32_t completed;
  void *copyprivate;

  // for critical construct
  omp_lock_t critical_lock;
  // for atomic construct
  omp_lock_t atomic_lock;
} work_t;

extern event_t event;
extern work_t works;
#endif /* __LIBGOMP_H__ */
