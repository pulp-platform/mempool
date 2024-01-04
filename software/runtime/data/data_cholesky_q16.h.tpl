// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '(int16_t) 0X{:04X}, '.format(a&0xffff)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define dim_N (${n_matrix})
#define N_SAMPLES (${n_samples})
int16_t l2_GIn[2 * ${n_samples * n_matrix * n_matrix}] = ${array_to_cstr(G)};
int16_t l2_LOut[2 * ${n_samples * n_matrix * n_matrix}] = ${array_to_cstr(L)};
