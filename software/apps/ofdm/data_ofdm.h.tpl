// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '{}, '.format(a)
        i += 1
        if i % 32 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define N_RX (${N_rx})
#define N_BEAMS (${N_bs})
#define N_SC (${N_sc})
#define N_SB (${N_sb})

int16_t l2_pFFT_src[${2 * N_sc * N_rx * N_sb}] = ${array_to_cstr(pFFT_src)};

int16_t l2_pTw_coef[${int(4 * N_sc)}] = ${array_to_cstr(pTw_coef)};

int16_t l2_pBF_coef[${2 * N_sc * N_sb * N_bs}] = ${array_to_cstr(pBF_coef)};
