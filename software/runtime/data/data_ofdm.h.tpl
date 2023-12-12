// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '(__fp16){:0.5}f, '.format(a)
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

#define LOG2 (${Log2Len})
#define N_RX (${N_rx})
#define N_BEAMS (${N_bs})
#define N_SC (${N_sc})
#define N_BANKS (NUM_CORES * BANKING_FACTOR)
#define BITREVINDEXTABLE_LENGTH (${BitrevLen})


__fp16 l2_pFFT_Src[${2 * N_sc * N_rx}] = ${array_to_cstr(pFFT_src)};

__fp16 l2_twiddleCoef_f16[${2 * N_sc}] = ${array_to_cstr(pTw_coef)};

__fp16 l2_pBF_Coef[${2 * N_bs * N_rx}] = ${array_to_cstr(pBF_coef)};

__fp16 l2_pBF_Dst[${2 * N_bs * N_sc}] = ${array_to_cstr(pBF_dst)};

// Bitreversal
uint16_t l2_BitRevIndexTable[${BitrevLen}] = ${array_to_str(bitrev)};
