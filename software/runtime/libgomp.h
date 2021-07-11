#ifndef __LIBGOMP_H__
#define __LIBGOMP_H__

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "omp.h"
#include "omp-lock.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define WS_INITED       ( 0xfeeddeadU )
#define WS_NOT_INITED   ( 0x0U )

/* barrier.c */
extern void GOMP_barrier (void);

/* single.c */
extern int GOMP_single_start(void);
extern void *GOMP_single_copy_start(void);
extern void GOMP_single_copy_end(void *);

/* critical.c */
extern void GOMP_critical_start (void);
extern void GOMP_critical_end (void);
extern void GOMP_atomic_start (void);
extern void GOMP_atomic_end (void);

/* loop.c */
extern int GOMP_loop_dynamic_start(int start, int end, int incr, int chunk_size, int *istart, int *iend);
extern int GOMP_loop_dynamic_next (int *istart, int *iend);
extern void GOMP_parallel_loop_dynamic (void (*fn) (void *), void *data, unsigned num_threads, long start, long end, long incr, long chunk_size);
extern void GOMP_loop_end(void);
extern void GOMP_loop_end_nowait(void);

/* parallel.c */
extern void GOMP_parallel (void (*fn) (void*), void *data, unsigned int num_threads, unsigned int flags);
extern void GOMP_parallel_start (void (*fn) (void*), void *data, unsigned int num_threads);
extern void GOMP_parallel_end (void);

/* sections.c */
extern void GOMP_parallel_sections(void (*) (void *), void *, unsigned int, int);
extern int GOMP_sections_start (int);
extern void GOMP_sections_end(void);
extern void GOMP_sections_end_nowait(void);
extern int GOMP_sections_next(void);
extern void GOMP_parallel_sections_start(void (*) (void *), void *, unsigned, unsigned);

/* work.c */
extern void gomp_new_work_share(void);
extern int gomp_work_share_start (void);

extern void set_event(void (*fn) (void*), void *data, uint32_t nthreads);
extern void run_task(uint32_t core_id);

typedef struct {
  void (*fn) (void*);
  void *data;
  uint32_t nthreads;
  uint32_t barrier;
  uint8_t thread_pool[16];
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
#endif  /* __LIBGOMP_H__ */
