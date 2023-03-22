// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#ifdef TEST_64

/**
  @par
  Example code for q15 Twiddle factors Generation::
  @par
  <pre>for (i = 0; i< 3N/4; i++)
  {
     twiddleCoefq15[2*i]   = cos(i * 2*PI/(float)N);
     twiddleCoefq15[2*i+1] = sin(i * 2*PI/(float)N);
  } </pre>
  @par
  where N = 64, PI = 3.14159265358979
  @par
  Cos and Sin values are interleaved fashion
  @par
  Convert Floating point to q15(Fixed point 1.15):
        round(twiddleCoefq15(i) * pow(2, 15))
 */
int16_t twiddleCoef_q16[96] = {
    (int16_t)0x7FFF, (int16_t)0x0000, (int16_t)0x7F62, (int16_t)0x0C8B,
    (int16_t)0x7D8A, (int16_t)0x18F8, (int16_t)0x7A7D, (int16_t)0x2528,
    (int16_t)0x7641, (int16_t)0x30FB, (int16_t)0x70E2, (int16_t)0x3C56,
    (int16_t)0x6A6D, (int16_t)0x471C, (int16_t)0x62F2, (int16_t)0x5133,
    (int16_t)0x5A82, (int16_t)0x5A82, (int16_t)0x5133, (int16_t)0x62F2,
    (int16_t)0x471C, (int16_t)0x6A6D, (int16_t)0x3C56, (int16_t)0x70E2,
    (int16_t)0x30FB, (int16_t)0x7641, (int16_t)0x2528, (int16_t)0x7A7D,
    (int16_t)0x18F8, (int16_t)0x7D8A, (int16_t)0x0C8B, (int16_t)0x7F62,
    (int16_t)0x0000, (int16_t)0x7FFF, (int16_t)0xF374, (int16_t)0x7F62,
    (int16_t)0xE707, (int16_t)0x7D8A, (int16_t)0xDAD7, (int16_t)0x7A7D,
    (int16_t)0xCF04, (int16_t)0x7641, (int16_t)0xC3A9, (int16_t)0x70E2,
    (int16_t)0xB8E3, (int16_t)0x6A6D, (int16_t)0xAECC, (int16_t)0x62F2,
    (int16_t)0xA57D, (int16_t)0x5A82, (int16_t)0x9D0D, (int16_t)0x5133,
    (int16_t)0x9592, (int16_t)0x471C, (int16_t)0x8F1D, (int16_t)0x3C56,
    (int16_t)0x89BE, (int16_t)0x30FB, (int16_t)0x8582, (int16_t)0x2528,
    (int16_t)0x8275, (int16_t)0x18F8, (int16_t)0x809D, (int16_t)0x0C8B,
    (int16_t)0x8000, (int16_t)0x0000, (int16_t)0x809D, (int16_t)0xF374,
    (int16_t)0x8275, (int16_t)0xE707, (int16_t)0x8582, (int16_t)0xDAD7,
    (int16_t)0x89BE, (int16_t)0xCF04, (int16_t)0x8F1D, (int16_t)0xC3A9,
    (int16_t)0x9592, (int16_t)0xB8E3, (int16_t)0x9D0D, (int16_t)0xAECC,
    (int16_t)0xA57D, (int16_t)0xA57D, (int16_t)0xAECC, (int16_t)0x9D0D,
    (int16_t)0xB8E3, (int16_t)0x9592, (int16_t)0xC3A9, (int16_t)0x8F1D,
    (int16_t)0xCF04, (int16_t)0x89BE, (int16_t)0xDAD7, (int16_t)0x8582,
    (int16_t)0xE707, (int16_t)0x8275, (int16_t)0xF374, (int16_t)0x809D};
#endif