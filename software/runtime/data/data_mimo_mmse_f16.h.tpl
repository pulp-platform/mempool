// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '{}f, '.format(a)
        i += 1
        if i % 8 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define N_TX (${N_tx})
#define N_RX (${N_rx})
#define N_ITR (${N_itr})

// Inputs

__fp16 In_H[${2 * N_tx * N_rx * N_itr}] = ${array_to_cstr(H)};

__fp16 In_G[${2 * N_tx * N_tx * N_itr}] = ${array_to_cstr(G)};

__fp16 In_b[${2 * N_rx * N_itr}] = ${array_to_cstr(b)};

__fp16 In_sigma[${N_tx * N_itr}] = ${array_to_cstr(sigma)};

// Outputs

__fp16 Out_x[${2 * N_tx * N_itr}] = ${array_to_cstr(x)};
