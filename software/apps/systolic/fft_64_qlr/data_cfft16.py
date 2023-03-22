#!/usr/bin/env python3

import numpy as np
import argparse
import pathlib
from mako.template import Template


##################
# compute_result #
##################


def compute_result(inp, len):
    """
    Funciton to generate the expected result of the testcase.

    Arguments
    ---------
    input: numpy array of inputs
    env: Length of the input transform.
    """

    # Q16:
    # len=16:    Q1.15 -> Q5.11
    # len=32:    Q1.15 -> Q6.10
    # len=64:    Q1.15 -> Q7.9
    # len=128:   Q1.15 -> Q8.8
    # len=256:   Q1.15 -> Q9.7
    # len=512:   Q1.15 -> Q10.6
    # len=1024:  Q1.15 -> Q11.5
    # len=2048:  Q1.15 -> Q12.4
    # len=4096:  Q1.15 -> Q13.3
    bit_shift_dict_q16 = {16:11, 32:10, 64: 9, 128: 8, 256: 7, 512: 6, 1024: 5, 2048: 4, 4096: 3}
    my_type = np.int16
    my_fixpoint = 15
    bit_shift_dict = bit_shift_dict_q16
    a = inp.astype(my_type)
    result = np.zeros(a.size, dtype=my_type)
    complex_a = np.zeros(int(a.size/2), dtype=np.csingle)
    complex_result = np.zeros(a.size>>1, dtype=np.csingle)
    for i in range(a.size>>1):
        complex_a[i] = a[2*i].astype(np.csingle)/(2**(my_fixpoint)) + (a[2*i + 1].astype(np.csingle)/(2**(my_fixpoint)))*1j
    complex_result = np.fft.fft(complex_a)
    for i in range(int(a.size/2)):
        result[2*i] = (np.real(complex_result[i])*(2**(bit_shift_dict[int(a.size/2)]))).astype(my_type)
        result[2*i+1] = (np.imag(complex_result[i])*(2**(bit_shift_dict[int(a.size/2)]))).astype(my_type)

    return result

def gen_data_header_file(outdir: pathlib.Path.cwd(), tpl: pathlib.Path.cwd(), **kwargs):

    file = outdir / f"data_{kwargs['name']}.h"

    print(tpl, outdir, kwargs['name'])

    template = Template(filename=str(tpl))
    with file.open('w') as f:
        f.write(template.render(**kwargs))

def main():

    parser = argparse.ArgumentParser(description='Generate data for kernels')
    parser.add_argument(
        "-o",
        "--outdir",
        type=pathlib.Path,
        default=pathlib.Path.cwd(),
        required=False,
        help='Select out directory of generated data files'
    )
    parser.add_argument(
        "-t",
        "--tpl",
        type=pathlib.Path,
        required=False,
        default=pathlib.Path.cwd() / "data_cfftq16.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-d",
        "--dimension",
        type=int,
        required=False,
        default=64,
        help='Input dimension'
    )

    args = parser.parse_args()

    # Create sparse matrix
    Len = args.dimension
    Input = np.random.randint(-2**(15), 2**(15)-1, 2 * Len, dtype=np.int16)
    Result = compute_result(Input, Len)

    tolerance = {16:16, 32:20, 64:24, 128:28, 256:32, 512:48, 1024:64, 2048:96, 4096:128}
    if Len == 64:
        Lenstring = 'TEST_64'
    elif Len == 256:
        Lenstring = 'TEST_256'
    elif Len == 512:
        Lenstring = 'TEST_512'
    elif Len == 1024:
        Lenstring = 'TEST_1024'
    elif Len == 2048:
        Lenstring = 'TEST_2048'
    elif Len == 4096:
        Lenstring = 'TEST_4096'

    kwargs = {'name': 'cfftq16', 'vector_inp': Input, 'vector_res': Result, 'Len' : Len, 'Lenstring' : Lenstring, 'tolerance': tolerance[int(Len)]}

    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()

######################
# Fixpoint Functions #
######################


def q_sat(x):
    if x > 2**31 - 1:
        return x - 2**32
    elif x < -2**31:
        return x + 2**32
    else:
        return x


def q_add(a, b):
    return q_sat(a + b)


def q_sub(a, b):
    return q_sat(a - b)


def q_mul(a, b, p):
    return q_roundnorm(a * b, p)


def q_roundnorm(a, p):
    rounding = 1 << (p - 1)
    return q_sat((a + rounding) >> p)