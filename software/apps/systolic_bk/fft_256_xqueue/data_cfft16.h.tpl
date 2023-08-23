// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
\
<% def array_to_cstr(array):
    out = '{'
    i = 0
    out += '\n'
    for a in array:
        out += '{}, '.format(a)
        i += 1
        if i % 2 == 0:
            out += '\n'
    out = out[:-2] + '}'
    return out
%> \

#define ${Lenstring}
#define TOLERANCE (${tolerance})

% for m, m_str in zip([vector_inp, vector_res], ['vector_inp', 'vector_res']):

// Data arrays for matrix ${m_str}
int16_t ${m_str}[${2*Len}] = ${array_to_cstr(m)};

% endfor \
