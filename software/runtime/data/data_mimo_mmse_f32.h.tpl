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

float l2_H[${2 * N_tx * N_rx * N_itr}] = ${array_to_cstr(H)};

float l2_G[${2 * N_tx * N_tx * N_itr}] = ${array_to_cstr(G)};

float l2_y[${2 * N_rx * N_itr}] = ${array_to_cstr(y)};

float l2_Sigma[${N_tx * N_itr}] = ${array_to_cstr(sigma)};

// Outputs

float l2_x[${2 * N_tx * N_itr}] = ${array_to_cstr(x)};
