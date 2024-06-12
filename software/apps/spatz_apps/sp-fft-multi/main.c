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
#include "data/data_fft.h"

#define USE_DMA

static inline int fp_check(const float a, const float b) {
  const float threshold = 0.01f;

  // Absolute value
  float comp = a - b;
  if (comp < 0)
    comp = -comp;

  return comp > threshold;
}

// max(#Core) = (NFFT/4)/(N_FU)
// Helper index in 16-bits, needs to fit in a vector word (1/2 * 1/(N_FU))
// We also need to one additional round for strided store into bitrev order (another 1/2)
// 256  -> 16
// 512  -> 32
// 1024 -> 64

int main() {
  // twiddle layout: [re_p1, im_p1, re_p2, im_p2]
  const unsigned int num_cores = mempool_get_core_count();
  const unsigned int cid = mempool_get_core_id();
  mempool_barrier_init(cid);
  const uint32_t NFFTpc = NFFT / active_cores;

  const uint32_t tot_cores = active_cores * num_fft;
  // 32-bit floating, 4 byte distance in memory
  const uint32_t element_size = 4;
  // elements distance between two stores
  const uint32_t stride_e = active_cores;
  // distance in bits
  const uint32_t stride = stride_e * element_size;

  const uint32_t CHECK = 0;


  // Reset timer
  unsigned int timer = (unsigned int)-1;
  for (uint32_t n_fft = 0; n_fft < num_fft; n_fft ++) {
    if (cid == 0) {
      // DMA has a problem with copying unaligned L1 and L2 data
      // Twiddle's size may not be a power of 2, so we'd better use mannual copy instead of DMA

      dma_memcpy_blocking(samples[n_fft],     samples_dram,   (NFFT*2) * sizeof(float));
      // Not necessary, but can make sure address of samples, buffer and out are aligned
      dma_memcpy_blocking(buffer[n_fft],      buffer_dram,    (NFFT*2) * sizeof(float));
      dma_memcpy_blocking(out[n_fft],         buffer_dram,    (NFFT*2) * sizeof(float));

    #ifdef USE_DMA
      dma_memcpy_blocking(twiddle_p1[n_fft],  twiddle_dram,   (NTWI_P1*2) * sizeof(float));
      dma_memcpy_blocking(twiddle_p1[n_fft],  twiddle_dram,   (NTWI_P1*2) * sizeof(float));
      dma_memcpy_blocking(store_idx[n_fft],   store_idx_dram, (log2_nfft2-1) * (NFFTpc >> 1) * sizeof(uint16_t));
      dma_memcpy_blocking(core_offset[n_fft], coffset_dram,   active_cores * sizeof(uint32_t));

      float *p2_twi = twiddle_p2[n_fft];
      float *p2_twi_dram = twiddle_dram + (NTWI_P1<<1);
      for (uint32_t i = 0; i < active_cores; i ++) {
        dma_memcpy_blocking(p2_twi,  p2_twi_dram,   (NTWI_P2*2) * sizeof(float));
        p2_twi += (NTWI_P2*2);
      }
      printf("finish copy fft %u!\n", n_fft);
    #else
      if (CHECK)
        printf("load twi part 1\n");
      for (uint32_t i = 0; i < 2*NTWI_P1; i++) {
        twiddle_p1[n_fft][i]   = twiddle_dram[i];
      }
    #endif
    }

    #ifndef USE_DMA
    if (cid < active_cores) {
      if ((cid == 0) & CHECK) {
        printf("load twi part 2\n");
      }
      for (uint32_t i = cid*(NTWI_P2*2); i < (cid+1)*(NTWI_P2*2); i++) {
        // Each core has its own P2 twiddle copy to reduce bank conflicts
        // parallel the load across multi cores
        twiddle_p2[n_fft][i] = twiddle_dram[i + (NTWI_P1<<1)];
      }
    }

    if (cid == 0) {
      for (uint32_t i = 0; i < (log2_nfft2-1) * (NFFTpc >> 1); i++) {
        // Each stages in phase 2 except last one need store index
        store_idx[n_fft][i] = store_idx_dram[i];
      }

      for (uint32_t i = 0; i < active_cores; i++) {
        // The offset of address used to calculate the pointer
        core_offset[n_fft][i]    = coffset_dram[i];
      }

      printf("finish copy fft %u!\n", n_fft);
    }
    #endif
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);


  uint32_t n_fft_id  = cid / active_cores;
  uint32_t n_fft_cid = cid - active_cores * n_fft_id;

  // Calculate pointers for the second butterfly onwards
  float *src_p2 = samples[n_fft_id] + n_fft_cid * NFFTpc;
  float *buf_p2 = buffer[n_fft_id]  + n_fft_cid * NFFTpc;
  // Let each core has its own twiddle copy to reduce bank conflicts
  // TODO: Optimize for MemPool data layout
  float *twi_p2 = twiddle_p2[n_fft_id] + n_fft_cid * (NTWI_P2<<1);
  float *out_p2 = out[n_fft_id] + core_offset[n_fft_id][n_fft_cid];

  uint32_t  p2_switch = 0;

  float *src_p1 = samples[n_fft_id];
  float *buf_p1 = buffer[n_fft_id];
  float *twi_p1 = twiddle_p1[n_fft_id];
  const uint32_t len = (NFFTpc >> 1);

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Start timer
  if (cid < tot_cores) {
    mempool_start_benchmark();
    timer = mempool_get_timer();
  }

  for (uint32_t i = 0; i < log2_nfft1; i ++) {
    if (cid < tot_cores) {
      fft_p1(src_p1, buf_p1, twi_p1, NFFT, NTWI_P1, n_fft_cid, active_cores, i, len);
      // each round will use half the twiddle than previous round
      // the first round needs re/im NFFT/2 twiddles

      src_p1 = (i & 1) ? samples[n_fft_id] : buffer[n_fft_id];
      buf_p1 = (i & 1) ? buffer[n_fft_id]  : samples[n_fft_id];
      twi_p1 += (NFFT >> (i+1));
      p2_switch = (i & 1);
    }
    // In first part of calculation, we need barrier after each round
    mempool_barrier(num_cores);
  }

  if (cid < tot_cores) {
    // Fall back into the single-core case
    // Each core just do a FFT on (NFFT >> stage_in_P1) data
    if (p2_switch) {
      fft_p2(buf_p2, src_p2, twi_p2, out_p2, store_idx[n_fft_id], (NFFT>>log2_nfft1),
             NFFT, log2_nfft2, stride, log2_nfft1, NTWI_P2);
    } else {
      fft_p2(src_p2, buf_p2, twi_p2, out_p2, store_idx[n_fft_id], (NFFT>>log2_nfft1),
             NFFT, log2_nfft2, stride, log2_nfft1, NTWI_P2);
    }
  }
  // Wait for all cores to finish fft
  mempool_barrier(num_cores);

  // End timer and check if new best runtime
  if (cid < tot_cores) {
    timer = mempool_get_timer()- timer;
    mempool_stop_benchmark();
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

    if (CHECK) {
      uint32_t rerror = 0;
      uint32_t ierror = 0;

      for (uint32_t n_fft = 0; n_fft < num_fft; n_fft ++) {
        rerror = 0;
        ierror = 0;

        // Verify the real part
        for (unsigned int i = 0; i < NFFT; i++) {
          if (fp_check(out[n_fft_id][i], gold_out_dram[2 * i])) {
            rerror ++;
          }
        }

        // Verify the imac part
        for (unsigned int i = 0; i < NFFT; i++) {
          if (fp_check(out[n_fft_id][i + NFFT], gold_out_dram[2 * i + 1])) {
            ierror ++;
          }
        }

        printf ("fft%u r:%d,i:%d\n", n_fft, rerror, ierror);
      }
    }
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return 0;
}
