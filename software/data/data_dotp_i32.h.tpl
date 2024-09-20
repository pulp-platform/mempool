// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '{}, '.format(a)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define LEN (${Len})

int32_t __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_A[${Len}] = ${array_to_cstr(A)};

int32_t __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_B[${Len}] = ${array_to_cstr(B)};

int32_t __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_C = ${C};