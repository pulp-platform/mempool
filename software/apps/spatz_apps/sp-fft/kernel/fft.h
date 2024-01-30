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

// Author: Diyou Shen, Matteo Perotti, ETH Zurich

#include <stdint.h>
#include <string.h>

#ifndef _FFT_H_
#define _FFT_H_

// Phase 1 of vector FFT on muti-core
inline void fft_p1 (float *src, float *buf, const float *twi,
                    const uint32_t nfft,  const uint32_t ntwi, 
                    const uint32_t cid,   const uint32_t num_cores,
                    const uint32_t stage, const uint32_t len)
    __attribute__((always_inline));

// Phase 2 of vector FFT on muti-core
inline void fft_p2(float *s, float *buf, const float *twi, float *out,
                   const uint16_t *seq_idx, const uint32_t nfft,
                   const uint32_t nfft_ori, const uint32_t log2_nfft, 
                   const uint32_t stride,   const uint32_t stride_e, const uint32_t ntwi)
    __attribute__((always_inline));

#endif
