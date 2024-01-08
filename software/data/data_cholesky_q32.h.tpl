// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '(int32_t) 0X{:08X}, '.format(a&0xffffffff)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define N (${n_matrix})

int32_t __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_GIn[${n_matrix * n_matrix}] = ${array_to_cstr(G)};
int32_t __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_LOut[${n_matrix * n_matrix}] = ${array_to_cstr(L)};
int32_t __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_y[${n_matrix}] = ${array_to_cstr(y)};
