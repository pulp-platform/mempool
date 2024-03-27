// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '(__fp16){:.4f}f, '.format(a)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define matrix_M (${matrix_M})
#define matrix_N (${matrix_N})
#define matrix_P (${matrix_P})

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) A[${matrix_M * matrix_N}] = ${array_to_cstr(A)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) B[${matrix_N * matrix_P}] = ${array_to_cstr(B)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) C[${matrix_M * matrix_P}] = ${array_to_cstr(C)};
