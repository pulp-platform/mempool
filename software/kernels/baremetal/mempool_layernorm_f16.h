// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"

void layernorm_f16s(__fp16 *input, __fp16 *output, uint32_t N, float eps,
                    float gamma, float beta, uint32_t relu) {

  float mean = 0.0f;
  float var = 0.0f;
  float Nf;
  v2h x, tmp;
  v2h vmean, vvar, vgamma, vbeta;
  uint32_t i;

  // Mean
  for (i = 0; i < N; i += 2) {
    x = *(v2h *)&(input[i]);
    asm volatile("vfdotpex.s.h %[mean], %[x], %[ones];"
                 : [mean] "+r"(mean)
                 : [x] "r"(x), [ones] "r"(0x3c003c00)
                 :);
  }
  asm volatile("fcvt.s.wu  %0, %1;" : "=r"(Nf) : "r"(N));
  asm volatile("fdiv.s %0, %0, %1;" : "+r"(mean) : "r"(Nf));

  // Pack vectors for scaling
  asm volatile("vfcpka.h.s   %0, %1, %1;" : "=r"(vgamma) : "r"(gamma));
  asm volatile("vfcpka.h.s   %0, %1, %1;" : "=r"(vbeta) : "r"(beta));
  asm volatile("vfcpka.h.s   %0, %1, %1;" : "=r"(vmean) : "r"(mean));

  // Variance
  for (i = 0; i < N; i += 2) {
    x = *(v2h *)&(input[i]);
    asm volatile(
        // Accumulate sum of squares for variance calculation
        "vfsub.h        %[tmp], %[x], %[vmean];" // tmp = input[i] - mean
        "vfdotpex.s.h   %[var], %[tmp], %[tmp];" // var += (x - mean)^2
        : [var] "+&r"(var), [tmp] "+&r"(tmp)
        : [x] "r"(x), [vmean] "r"(vmean)
        : "memory");
  }
  asm volatile("fdiv.s %0, %0, %1;" : "+&r"(var) : "r"(Nf));

  // Layernorm
  asm volatile("fadd.s %0, %0, %1;" : "+&r"(var) : "r"(eps));
  asm volatile("fsqrt.s %0, %0;" : "+&r"(var));
  asm volatile("vfcpka.h.s %0, %1, %1;" : "+&r"(vvar) : "r"(var));
  for (i = 0; i < N; i += 2) {
    x = *(v2h *)&(input[i]);
    asm volatile(
        "vfsub.h      %[tmp], %[x],   %[vmean];"  // x - mean
        "vfdiv.h      %[tmp], %[tmp], %[vvar];"   // (x - mean) / sqrt(var)
        "vfmul.h      %[tmp], %[tmp], %[vgamma];" // * gamma
        "vfadd.h      %[tmp], %[tmp], %[vbeta];"  // + beta
        : [tmp] "+&r"(tmp)
        : [x] "r"(x), [vmean] "r"(vmean), [vvar] "r"(vvar),
          [vgamma] "r"(vgamma), [vbeta] "r"(vbeta)
        :);

    // ReLU
    if (relu == 1) {
      uint32_t msk1 = 0x00020002;
      uint32_t msk2 = 0xFFFF0000;
      uint32_t cmp;
      asm volatile("vfge.h        %[cmp], %[tmp], zero;"
                   "or            %[cmp], %[cmp], %[msk1];"
                   "pv.shuffle2.h %[cmp], %[msk2], %[cmp];"
                   "and           %[tmp], %[tmp], %[cmp];"
                   : [cmp] "+&r"(cmp), [tmp] "+&r"(tmp)
                   : [msk1] "r"(msk1), [msk2] "r"(msk2));
      printf("%8x\n", cmp);
    }
    *((v2h *)&output[i]) = tmp;
  }

  return;
}

void layernorm_f16s_unrolled4(__fp16 *input, __fp16 *output, uint32_t N,
                              float eps, float gamma, float beta,
                              uint32_t relu) {

  v2h x0, x1, x2, x3;
  v2h t0, t1, t2, t3;

  float m0 = 0.0f;
  float m1 = 0.0f;
  float m2 = 0.0f;
  float m3 = 0.0f;

  float v0 = 0.0f;
  float v1 = 0.0f;
  float v2 = 0.0f;
  float v3 = 0.0f;

  float Nf;
  v2h vmean, vvar, vgamma, vbeta;
  uint32_t i;

  // Mean
  for (i = 0; i < N; i += 8) {
    x0 = *(v2h *)&(input[i + 0]);
    x1 = *(v2h *)&(input[i + 2]);
    x2 = *(v2h *)&(input[i + 4]);
    x3 = *(v2h *)&(input[i + 6]);
    asm volatile("vfdotpex.s.h %[m0], %[x0], %[ones];"
                 "vfdotpex.s.h %[m1], %[x1], %[ones];"
                 "vfdotpex.s.h %[m2], %[x2], %[ones];"
                 "vfdotpex.s.h %[m3], %[x3], %[ones];"
                 : [m0] "+r"(m0), [m1] "+r"(m1), [m2] "+r"(m2), [m3] "+r"(m3)
                 : [x0] "r"(x0), [x1] "r"(x1), [x2] "r"(x2), [x3] "r"(x3),
                   [ones] "r"(0x3c003c00)
                 :);
  }
  asm volatile("fadd.s  %0, %0, %1;" : "+&r"(m0) : "r"(m1));
  asm volatile("fadd.s  %0, %0, %1;" : "+&r"(m2) : "r"(m3));
  asm volatile("fadd.s  %0, %0, %1;" : "+&r"(m0) : "r"(m2));
  asm volatile("fcvt.s.wu  %0, %1;" : "=r"(Nf) : "r"(N));
  asm volatile("fdiv.s %0, %0, %1;" : "+r"(m0) : "r"(Nf));

  // Pack vectors for scaling
  asm volatile("vfcpka.h.s   %0, %1, %1;" : "=r"(vgamma) : "r"(gamma));
  asm volatile("vfcpka.h.s   %0, %1, %1;" : "=r"(vbeta) : "r"(beta));
  asm volatile("vfcpka.h.s   %0, %1, %1;" : "=r"(vmean) : "r"(m0));

  // Variance
  for (i = 0; i < N; i += 8) {
    x0 = *(v2h *)&(input[i + 0]);
    x1 = *(v2h *)&(input[i + 2]);
    x2 = *(v2h *)&(input[i + 4]);
    x3 = *(v2h *)&(input[i + 6]);
    asm volatile(
        // Accumulate sum of squares for variance calculation
        "vfsub.h        %[t0], %[x0], %[vmean];" // tmp = input[i] - mean
        "vfsub.h        %[t1], %[x1], %[vmean];"
        "vfsub.h        %[t2], %[x2], %[vmean];"
        "vfsub.h        %[t3], %[x3], %[vmean];"
        "vfdotpex.s.h   %[v0], %[t0], %[t0];" // var += (x - mean)^2
        "vfdotpex.s.h   %[v1], %[t1], %[t1];"
        "vfdotpex.s.h   %[v2], %[t2], %[t2];"
        "vfdotpex.s.h   %[v3], %[t3], %[t3];"
        : [v0] "+r"(v0), [v1] "+r"(v1), [v2] "+r"(v2), [v3] "+r"(v3),
          [t0] "+&r"(t0), [t1] "+&r"(t1), [t2] "+&r"(t2), [t3] "+&r"(t3)
        : [x0] "r"(x0), [x1] "r"(x1), [x2] "r"(x2), [x3] "r"(x3),
          [vmean] "r"(vmean)
        :);
  }
  asm volatile("fadd.s  %0, %0, %1;" : "+&r"(v0) : "r"(v1));
  asm volatile("fadd.s  %0, %0, %1;" : "+&r"(v2) : "r"(v3));
  asm volatile("fadd.s  %0, %0, %1;" : "+&r"(v0) : "r"(v2));
  asm volatile("fdiv.s %0, %0, %1;" : "+&r"(v0) : "r"(Nf));

  // Layernorm
  asm volatile("fadd.s %0, %0, %1;" : "+&r"(v0) : "r"(eps));
  asm volatile("fsqrt.s %0, %0;" : "+&r"(v0));
  asm volatile("vfcpka.h.s %0, %1, %1;" : "+&r"(vvar) : "r"(v0));
  for (i = 0; i < N; i += 8) {
    x0 = *(v2h *)&(input[i + 0]);
    x1 = *(v2h *)&(input[i + 2]);
    x2 = *(v2h *)&(input[i + 4]);
    x3 = *(v2h *)&(input[i + 6]);
    asm volatile(
        "vfsub.h  %[t0], %[x0], %[vmean];" // x - mean
        "vfsub.h  %[t1], %[x1], %[vmean];"
        "vfsub.h  %[t2], %[x2], %[vmean];"
        "vfsub.h  %[t3], %[x3], %[vmean];"
        "vfdiv.h  %[t0], %[t0], %[vvar];" // (x - mean) / sqrt(var)
        "vfdiv.h  %[t1], %[t1], %[vvar];"
        "vfdiv.h  %[t2], %[t2], %[vvar];"
        "vfdiv.h  %[t3], %[t3], %[vvar];"
        "vfmul.h  %[t0], %[t0], %[vgamma];" // * gamma
        "vfmul.h  %[t1], %[t1], %[vgamma];"
        "vfmul.h  %[t2], %[t2], %[vgamma];"
        "vfmul.h  %[t3], %[t3], %[vgamma];"
        "vfadd.h  %[t0], %[t0], %[vbeta];" // + beta
        "vfadd.h  %[t1], %[t1], %[vbeta];"
        "vfadd.h  %[t2], %[t2], %[vbeta];"
        "vfadd.h  %[t3], %[t3], %[vbeta];"
        : [t0] "+&r"(t0), [t1] "+&r"(t1), [t2] "+&r"(t2), [t3] "+&r"(t3)
        : [x0] "r"(x0), [x1] "r"(x1), [x2] "r"(x2), [x3] "r"(x3),
          [vmean] "r"(vmean), [vvar] "r"(vvar), [vgamma] "r"(vgamma),
          [vbeta] "r"(vbeta)
        : "memory");

    // ReLU
    if (relu == 1) {
      uint32_t msk1 = 0x00020002;
      uint32_t msk2 = 0xFFFF0000;
      uint32_t cmp0;
      uint32_t cmp1;
      uint32_t cmp2;
      uint32_t cmp3;
      asm volatile("vfge.h        %[cmp0], %[t0], zero;"
                   "vfge.h        %[cmp1], %[t1], zero;"
                   "vfge.h        %[cmp2], %[t2], zero;"
                   "vfge.h        %[cmp3], %[t3], zero;"
                   "or            %[cmp0], %[cmp0], %[msk1];"
                   "or            %[cmp1], %[cmp1], %[msk1];"
                   "or            %[cmp2], %[cmp2], %[msk1];"
                   "or            %[cmp3], %[cmp3], %[msk1];"
                   "pv.shuffle2.h %[cmp0], %[msk2], %[cmp0];"
                   "pv.shuffle2.h %[cmp1], %[msk2], %[cmp1];"
                   "pv.shuffle2.h %[cmp2], %[msk2], %[cmp2];"
                   "pv.shuffle2.h %[cmp3], %[msk2], %[cmp3];"
                   "and           %[t0], %[t0], %[cmp0];"
                   "and           %[t1], %[t1], %[cmp1];"
                   "and           %[t2], %[t2], %[cmp2];"
                   "and           %[t3], %[t3], %[cmp3];"
                   : [t0] "+&r"(t0), [t1] "+&r"(t1), [t2] "+&r"(t2),
                     [t3] "+&r"(t3), [cmp0] "+&r"(cmp0), [cmp1] "+&r"(cmp1),
                     [cmp2] "+&r"(cmp2), [cmp3] "+&r"(cmp3)
                   : [msk1] "r"(msk1), [msk2] "r"(msk2));
    }

    *((v2h *)&output[i + 0]) = t0;
    *((v2h *)&output[i + 2]) = t1;
    *((v2h *)&output[i + 4]) = t2;
    *((v2h *)&output[i + 6]) = t3;
  }
  return;
}

void relu_f16s_unrolled4(__fp16 *input, __fp16 *output) {

  v2h t0, t1, t2, t3;
  uint32_t i;
  // ReLU
  for (i = 0; i < N; i += 8) {
    x0 = *(v2h *)&(input[i + 0]);
    x1 = *(v2h *)&(input[i + 2]);
    x2 = *(v2h *)&(input[i + 4]);
    x3 = *(v2h *)&(input[i + 6]);
    uint32_t msk1 = 0x00020002;
    uint32_t msk2 = 0xFFFF0000;
    uint32_t cmp0;
    uint32_t cmp1;
    uint32_t cmp2;
    uint32_t cmp3;
    asm volatile("vfge.h        %[cmp0], %[x0], zero;"
                 "vfge.h        %[cmp1], %[x1], zero;"
                 "vfge.h        %[cmp2], %[x2], zero;"
                 "vfge.h        %[cmp3], %[x3], zero;"
                 "or            %[cmp0], %[cmp0], %[msk1];"
                 "or            %[cmp1], %[cmp1], %[msk1];"
                 "or            %[cmp2], %[cmp2], %[msk1];"
                 "or            %[cmp3], %[cmp3], %[msk1];"
                 "pv.shuffle2.h %[cmp0], %[msk2], %[cmp0];"
                 "pv.shuffle2.h %[cmp1], %[msk2], %[cmp1];"
                 "pv.shuffle2.h %[cmp2], %[msk2], %[cmp2];"
                 "pv.shuffle2.h %[cmp3], %[msk2], %[cmp3];"
                 "and           %[x0], %[x0], %[cmp0];"
                 "and           %[x1], %[x1], %[cmp1];"
                 "and           %[x2], %[x2], %[cmp2];"
                 "and           %[x3], %[x3], %[cmp3];"
                 : [x0] "+&r"(x0), [x1] "+&r"(x1), [x2] "+&r"(x2),
                   [x3] "+&r"(x3), [cmp0] "+&r"(cmp0), [cmp1] "+&r"(cmp1),
                   [cmp2] "+&r"(cmp2), [cmp3] "+&r"(cmp3)
                 : [msk1] "r"(msk1), [msk2] "r"(msk2));
    *((v2h *)&output[i + 0]) = x0;
    *((v2h *)&output[i + 2]) = x1;
    *((v2h *)&output[i + 4]) = x2;
    *((v2h *)&output[i + 6]) = x3;
  }
  return;
}
