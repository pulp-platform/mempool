// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '(__fp16){:.5f}, '.format(a)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define dim_M (${matrix_M})
#define dim_N (${matrix_N})
#define dim_P (${matrix_P})

__fp16 A[${2 * matrix_M * matrix_N}] = ${array_to_cstr(A)};

__fp16 B[${2 * matrix_N * matrix_P}] = ${array_to_cstr(B)};

__fp16 C[${2 * matrix_M * matrix_P}] = ${array_to_cstr(C)};
