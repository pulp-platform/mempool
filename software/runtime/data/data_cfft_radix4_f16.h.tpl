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
#define N_CSAMPLES (${Len})
#define N_RSAMPLES (2 * N_CSAMPLES)
#define N_TWIDDLES (3 * N_CSAMPLES / 4)
#define N_BANKS (NUM_CORES * BANKING_FACTOR)
#define BITREVINDEXTABLE_FIXED_TABLE_LENGTH (${BitrevLen})

__fp16 pSrc[${2 * Len}] = ${array_to_cstr(src)};

__fp16 pDst[${2 * Len}] = ${array_to_cstr(dst)};

__fp16 pTwi[${2 * Len}] = ${array_to_cstr(twi)};

// Bitreversal
uint16_t BitRevIndexTable[${BitrevLen}] = ${array_to_str(bitrev)};