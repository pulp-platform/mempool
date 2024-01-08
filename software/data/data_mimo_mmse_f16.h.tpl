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

<% def array_to_str(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '{}, '.format(a)
        i += 1
        if i % 16 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define N_TX (${N_tx})
#define N_RX (${N_rx})
#define N_ITR (${N_itr})

// Inputs

uint32_t __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_beamgroups[${N_itr}] = ${array_to_str(beamgroups)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_H[${2 * N_tx * N_rx * N_itr}] = ${array_to_cstr(H)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_G[${2 * N_tx * N_tx * N_itr}] = ${array_to_cstr(G)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_y[${2 * N_rx * N_itr}] = ${array_to_cstr(y)};

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_Sigma[${2 * N_tx * N_itr}] = ${array_to_cstr(sigma)};

// Outputs

__fp16 __attribute__((aligned(sizeof(int32_t)), section(".l2"))) l2_x[${2 * N_tx * N_itr}] = ${array_to_cstr(x)};