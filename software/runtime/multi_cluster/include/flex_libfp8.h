// Copyright 2025 ETH Zurich and University of Bologna.
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

// Author: Bowen Wang, ETH Zurich

// SoftHier Generic FP8 runtime support

#ifndef _FLEX_LIBFP8_H_
#define _FLEX_LIBFP8_H_


union FloatBits {
    float f;
    uint32_t u;
};

/*
  Format transform
*/

// Decode fp8 E5M2 into float32
float fp8_e5m2_to_f32(uint8_t val) {
    if (val == 0x00) return 0.0f;

    uint8_t sign = (val >> 7) & 0x1;
    uint8_t exp  = (val >> 2) & 0x1F;  // 5-bit exponent
    uint8_t frac = val & 0x03;         // 2-bit mantissa

    // Bias = 15
    int exp_val = exp - 15;

    // mantissa = 1 + frac / 4.0
    float mant = 1.0f + (frac * 0.25f);

    // Compute 2^exp_val for small integers without math.h
    float scale = 1.0f;
    if (exp_val >= 0) {
        for (int i = 0; i < exp_val; i++) scale *= 2.0f;
    } else {
        for (int i = 0; i < -exp_val; i++) scale *= 0.5f;
    }

    float result = mant * scale;
    return sign ? -result : result;
}

// Decode fp16 (IEEE 754, E5M10) into float32
float fp16_to_f32(uint16_t val) {
    if (val == 0x0000) return 0.0f;

    uint16_t sign = (val >> 15) & 0x1;
    uint16_t exp  = (val >> 10) & 0x1F;    // 5-bit exponent
    uint16_t frac = val & 0x3FF;           // 10-bit mantissa

    if (exp == 0x1F) {
        // Handle Inf / NaN
        float inf_val = 65504.0f; // Max FP16 value
        return sign ? -inf_val : inf_val;
    }

    float mant;
    int exp_val;

    if (exp == 0) {
        // Subnormal number
        exp_val = 1 - 15;
        mant = frac / 1024.0f;
    } else {
        // Normalized number
        exp_val = exp - 15;
        mant = 1.0f + (frac / 1024.0f);
    }

    // Compute 2^exp_val without math.h
    float scale = 1.0f;
    if (exp_val >= 0) {
        for (int i = 0; i < exp_val; i++) scale *= 2.0f;
    } else {
        for (int i = 0; i < -exp_val; i++) scale *= 0.5f;
    }

    float result = mant * scale;
    return sign ? -result : result;
}

/*
  Numerical verification
*/

void spatz_verify(uint32_t avl, uint8_t* act_vec, const uint8_t* exp_vec, const float tol) {
    uint8_t exp_fp8, act_fp8;
    float exp_f32, act_f32;
    uint32_t tot_err = 0;

    for (uint32_t i = 0; i < avl; i++) {
        exp_fp8 = exp_vec[i];
        act_fp8 = act_vec[i];
        exp_f32 = fp8_e5m2_to_f32(exp_fp8);
        act_f32 = fp8_e5m2_to_f32(act_fp8);

        float err = exp_f32 - act_f32;
        // if (exp_fp8 != act_fp8) {
        //     printf("%3d | exp: 0x%02x (%.5f), act: 0x%02x (%.5f), err: %.5f\n",
        //            i, exp_fp8, exp_f32, act_fp8, act_f32, err);
        //     tot_err += 1;
        // }
        if (err > tol || err < -tol) {
            printf("%3d | exp: 0x%02x (%.5f), act: 0x%02x (%.5f), err: %.5f\n",
                   i, exp_fp8, exp_f32, act_fp8, act_f32, err);
            tot_err += 1;
        }
    }

    printf("Errors above threshold (E5M2: %.3ff): %d out of %d\n", tol, tot_err, avl);
}

// for widening instruction checks
void spatz_verify_16(uint32_t avl, uint16_t* act_vec, const uint16_t* exp_vec, const float tol) {
    uint16_t exp_fp16, act_fp16;
    float exp_f32, act_f32;
    uint32_t tot_err = 0;

    for (uint32_t i = 0; i < avl; i++) {
        exp_fp16 = exp_vec[i];
        act_fp16 = act_vec[i];
        exp_f32 = fp16_to_f32(exp_fp16);
        act_f32 = fp16_to_f32(act_fp16);

        float err = exp_f32 - act_f32;
        if (err > tol || err < -tol) {
            printf("%3d | exp: 0x%04x (%.5f), act: 0x%04x (%.5f), err: %.5f\n",
                   i, exp_fp16, exp_f32, act_fp16, act_f32, err);
            tot_err += 1;
        }
    }

    printf("Errors above threshold (E5M2: %.3ff): %d out of %d\n", tol, tot_err, avl);
}

#endif