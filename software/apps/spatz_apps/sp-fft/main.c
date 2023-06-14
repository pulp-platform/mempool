// Copyright 2021 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Diyou Shen, ETH Zurich

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"


#include "kernel/fft.c"
// #include "data/data_256_2.h"
// #include "data/data_256_4.h"
// #include "data/data_256_8.h"
// #include "data/data_512_2.h"
// #include "data/data_512_4.h"
// #include "data/data_1024_2.h"
// #include "data/data_1024_4.h"
#include "data/data_1024_8.h"

dump(p1, 5)
// each bit of DUMP controls one dumping selection
uint32_t DUMP = 0;

static inline int fp_check(const float a, const float b) {
  const float threshold = 0.01f;

  // Absolute value
  float comp = a - b;
  if (comp < 0)
    comp = -comp;

  return comp > threshold;
}

int main() {
  // twiddle layout: [re_p1, im_p1, re_p2, im_p2]
  const unsigned int num_cores = mempool_get_core_count();
  const unsigned int cid = mempool_get_core_id();
  mempool_barrier_init(cid);
  const uint32_t NFFTpc = NFFT / active_cores;
  // 32-bit floating, 4 byte distance in memory
  const uint32_t element_size = 4;
  // elements distance between two stores
  const uint32_t stride_e = active_cores;
  // distance in bits
  const uint32_t stride = stride_e * element_size;

  // Reset timer
  unsigned int timer = (unsigned int)-1;
  if (cid == 0) { 
    // DMA has a problem with copying unaligned L1 and L2 data
    // Twiddle's size may not be a power of 2, so we'd better use mannual copy instead of DMA
    // TODO: Fix DMA and let it copy the data!
    dma_memcpy_blocking(samples,     samples_dram,   (NFFT*2) * sizeof(float));
    dma_memcpy_blocking(buffer,      buffer_dram,    (NFFT*2) * sizeof(float));
    dma_memcpy_blocking(out,         buffer_dram,    (NFFT*2) * sizeof(float));

    for (uint32_t i = 0; i < 2*NTWI_P1; i++) {
      twiddle_p1[i]   = twiddle_dram[i];
    }

    for (uint32_t i = 0; i < (active_cores*NTWI_P2*2); i++) {
      // Each core has its own P2 twiddle copy to reduce bank conflicts
      twiddle_p2[i] = twiddle_dram[i + (NTWI_P1<<1)];
    }

    for (uint32_t i = 0; i < (log2_nfft2-1) * (NFFTpc >> 1); i++) {
      // Each stages in phase 2 except last one need store index
      store_idx[i] = store_idx_dram[i];
    }

    for (uint32_t i = 0; i < (NFFTpc >> 1); i++) {
      bitrev[i]    = bitrev_dram[i];
    }

    for (uint32_t i = 0; i < active_cores; i++) {
      core_offset[i]    = coffset_dram[i];
    }

    printf("finish copy!\n");
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Calculate pointers for the second butterfly onwards
  float *src_p2 = samples + cid * NFFTpc;
  float *buf_p2 = buffer + cid * NFFTpc;
  // Let each core has its own twiddle copy to reduce bank conflicts
  // TODO: Optimize for MemPool data layout
  float *twi_p2 = twiddle_p2 + cid * (NTWI_P2<<1);
  float *out_p2 = out + core_offset[cid];
  
  uint32_t  p2_switch = 0;

  float *src_p1 = samples;
  float *buf_p1 = buffer;
  float *twi_p1 = twiddle_p1;
  const uint32_t len = (NFFTpc >> 1);

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Start timer
  if (cid < active_cores) {
    mempool_start_benchmark();
    timer = mempool_get_timer();
  }

  for (uint32_t i = 0; i < log2_nfft1; i ++) {
    if (cid < active_cores) {
      fft_p1(src_p1, buf_p1, twi_p1, NFFT, NTWI_P1, cid, active_cores, i, len);
      // each round will use half the twiddle than previous round
      // the first round needs re/im NFFT/2 twiddles
      src_p1 = (i & 1) ? samples : buffer;
      buf_p1 = (i & 1) ? buffer : samples;
      twi_p1 += (NFFT >> (i+1));
      p2_switch = (i & 1);
    }
    // first bit of DUMP
    if (DUMP & 1) {
      if (cid == 0) {
        uint32_t *out_p1 = (uint32_t *) src_p1;
        for (uint32_t i = 0; i < NFFT*2; i ++) {
          dump_p1((uint32_t) out_p1[i]);
        }
        printf("\n");
      }
    }
    mempool_barrier(num_cores);
  }

  if (cid < active_cores) {
    // Fall back into the single-core case
    // Each core just do a FFT on (NFFT >> stage_in_P1) data
    if (p2_switch) {
      fft_p2(buf_p2, src_p2, twi_p2, out_p2, store_idx, (NFFT>>log2_nfft1),
             NFFT, log2_nfft2, stride, log2_nfft1, NTWI_P2);
    } else {
      fft_p2(src_p2, buf_p2, twi_p2, out_p2, store_idx, (NFFT>>log2_nfft1),
             NFFT, log2_nfft2, stride, log2_nfft1, NTWI_P2);
    }
  }
  // Wait for all cores to finish fft
  mempool_barrier(num_cores);

  // End timer and check if new best runtime
  if (cid < active_cores) {
    timer = mempool_get_timer()- timer;
    mempool_stop_benchmark();
  }
  // second bit of DUMP
  if (cid == 0 && (DUMP & 2)) {
    uint32_t *out_dump = (uint32_t *) out;
    for (uint32_t i = 0; i < NFFT*2; i ++) {
      dump_p1((uint32_t) out_dump[i]);
    }
    printf("\n");
  }

  // Display runtime
  if (cid == 0) {
    // Each stage requires:
    // 2 add, 2 sub, 2 mul, 2 macc/msac
    // in total 10 operations on NFFT/2 real and NFFT/2 im elements

    // Divide by two so that the utilization in macc isntead of op
    long unsigned int performance =
        1000 * NFFT * 10 * log2_nfft / timer;
    long unsigned int utilization = performance / (2 * active_cores * N_FU);

    printf("\n----- fft on %d samples -----\n", NFFT);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %ld OP/1000cycle (%ld%%o utilization).\n",
           performance, utilization);

    uint32_t rerror = 0;
    uint32_t ierror = 0;

    // Verify the real part
    for (unsigned int i = 0; i < NFFT; i++) {
      if (fp_check(out[i], gold_out_dram[2 * i])) {
        rerror ++;
      }
    }

    // Verify the imac part
    for (unsigned int i = 0; i < NFFT; i++) {
      if (fp_check(out[i + NFFT], gold_out_dram[2 * i + 1])) {
        ierror ++;
      }
    }

    printf ("r:%d,i:%d\n", rerror, ierror);
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return 0;
}
