// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '(__fp16){:0.5f}f, '.format(a)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define dim_N (${n_matrix})
#define N_SAMPLES (${n_samples})

__fp16 In_G[2 * ${n_samples * n_matrix * n_matrix}] = ${array_to_cstr(G)};

__fp16 Out_L[2 * ${n_samples * n_matrix * n_matrix}] = ${array_to_cstr(L)};
