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
        if i % 16 == 0:
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

// Maximum number of independent FFT columns allowed
#define MAX_COL (N_BANKS / (N_CSAMPLES / 4))
// Tolerance for correctness check
#define TOLERANCE (${tolerance})

% for m, m_str in zip([vector_inp, vector_res], ['vector_inp', 'vector_res']):

// Data arrays for matrix ${m_str}
int16_t ${m_str}[${2*Len}] = ${array_to_cstr(m)};

% endfor \

// Twiddles
int16_t twiddleCoef_q16[${int(6*Len/4)}] = ${array_to_cstr(vector_twi)};

// Bitreversal
uint16_t BitRevIndexTable[${BitrevLen}] = ${array_to_str(vector_bitrev)};
