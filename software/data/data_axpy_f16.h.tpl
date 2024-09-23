// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '(__fp16){:.4f}, '.format(a)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define LEN (${Len})

__fp16 __attribute__((section(".l2"))) A = ${'(__fp16){:.4f}'.format(A)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_X[${Len}] = ${array_to_cstr(X)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_Y[${Len}] = ${array_to_cstr(Y)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_out[${Len}] = ${array_to_cstr(out)};
