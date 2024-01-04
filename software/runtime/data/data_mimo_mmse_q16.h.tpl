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

#define N_TX (${N_tx})
#define N_RX (${N_rx})
#define N_ITR (${N_itr})

// Inputs

int16_t l2_H[${2 * N_tx * N_rx * N_itr}] = ${array_to_cstr(H)};

int16_t l2_G[${2 * N_tx * N_tx * N_itr}] = ${array_to_cstr(G)};

int16_t l2_y[${2 * N_rx * N_itr}] = ${array_to_cstr(y)};

int16_t l2_Sigma[${2 * N_tx * N_itr}] = ${array_to_cstr(sigma)};

// Outputs

int16_t l2_x[${2 * N_tx * N_itr}] = ${array_to_cstr(x)};
