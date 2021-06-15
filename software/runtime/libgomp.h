#ifndef __LIBGOMP_H__
#define __LIBGOMP_H__

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "omp.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"


extern void GOMP_parallel (void (*fn) (void*), void *data, unsigned int num_threads);
extern void GOMP_parallel_start (void (*fn) (void*), void *data, unsigned int num_threads);
extern void GOMP_parallel_end (void);
extern void GOMP_parallel_loop_dynamic (void (*fn) (void *), void *data, unsigned num_threads, long start, long end, long incr, long chunk_size, unsigned flags);
extern void GOMP_loop_end_nowait();
extern void GOMP_loop_dynamic_next (int *istart, int *iend);




extern void set_event(void (*fn) (void*), void *data, uint32_t nthreads);
extern void run_task(uint32_t core_id);

typedef struct {
  void (*fn) (void*);
  void *data;
  uint32_t nthreads;
  uint32_t barrier;
  uint8_t thread_pool[16];
} event_t;

extern event_t event;

#endif  /* __LIBGOMP_H__ */
