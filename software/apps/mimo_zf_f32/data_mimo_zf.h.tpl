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

// Inputs

float In_H[${2 * N_tx * N_rx}] = ${array_to_cstr(H)};

float In_G[${2 * N_tx * N_tx}] = ${array_to_cstr(G)};

float In_b[${2 * N_rx}] = ${array_to_cstr(b)};

float In_sigma[${N_tx}] = ${array_to_cstr(sigma)};

// Outputs

float Out_L[${2 * N_tx * N_tx}] = ${array_to_cstr(L)};

float Out_x[${2 * N_tx}] = ${array_to_cstr(x)};

float Out_s[${2 * N_tx}] = ${array_to_cstr(s)};

float Out_y[${2 * N_tx}] = ${array_to_cstr(y)};
