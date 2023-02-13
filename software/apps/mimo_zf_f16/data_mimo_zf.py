#!/usr/bin/env python3

import numpy as np
import argparse
import pathlib
from mako.template import Template
from scipy.linalg import solve_triangular


##################
# compute_result #
##################

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
        default=pathlib.Path.cwd() / "data_mimo_zf.h.tpl",
        help='Path to mako template'
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action='store_true',
        help='Set verbose'
    )
    parser.add_argument(
        "-n",
        "--transmitters",
        type=int,
        required=False,
        default=4,
        help='First dimension.'
    )
    parser.add_argument(
        "-m",
        "--receivers",
        type=int,
        required=False,
        default=32,
        help='First dimension.'
    )

    args = parser.parse_args()
    N_tx=args.transmitters
    N_rx=args.receivers

    # Create channel matrix
    H = np.random.rand(N_rx, N_tx).astype(np.float16) + 1.j * np.random.rand(N_rx, N_tx).astype(np.float16)
    # Create input vector
    b = np.random.rand(N_rx).astype(np.float16) + 1.j * np.random.rand(N_rx).astype(np.float16)

    # Matrix to be inverted in ZF estimator
    H_h = (np.asmatrix(H).H)
    G = H_h * H
    # Cholesky decomposition
    L = np.linalg.cholesky(G)
    # Linear system solution
    s = np.transpose(np.dot(H_h, b))
    y = solve_triangular(L, s, lower=True)
    x = solve_triangular(np.transpose(L), y)

    s = np.transpose(np.dot(np.asmatrix(H).H, b))
    y = solve_triangular(L, s, lower=True)
    x = solve_triangular(np.transpose(L), y)

    H = np.reshape(H, (N_tx*N_rx, -1), order='C')
    G = np.reshape(G, (N_tx*N_tx, -1), order='C')
    L = np.reshape(L, (N_tx*N_tx, -1), order='C')
    H_RI = np.zeros(2*N_tx*N_rx)
    G_RI = np.zeros(2*N_tx*N_tx)
    L_RI = np.zeros(2*N_tx*N_tx)
    b_RI = np.zeros(2*N_rx)
    s_RI = np.zeros(2*N_tx)
    x_RI = np.zeros(2*N_tx)
    y_RI = np.zeros(2*N_tx)

    for i in range(N_tx*N_rx):
        H_RI[2*i]   = H[i].real
        H_RI[2*i+1] = H[i].imag
    for i in range(N_tx*N_tx):
        G_RI[2*i]   = G[i].real
        G_RI[2*i+1] = G[i].imag
        L_RI[2*i]   = L[i].real
        L_RI[2*i+1] = L[i].imag

    for i in range(N_rx):
        b_RI[2*i]   = b[i].real
        b_RI[2*i+1] = b[i].imag
    for i in range(N_tx):
        s_RI[2*i]   = s[i].real
        s_RI[2*i+1] = s[i].imag
        x_RI[2*i]   = x[i].real
        x_RI[2*i+1] = x[i].imag
        y_RI[2*i]   = y[i].real
        y_RI[2*i+1] = y[i].imag

    H_RI = H_RI.astype(np.float16)
    G_RI = G_RI.astype(np.float16)
    L_RI = L_RI.astype(np.float16)
    b_RI = b_RI.astype(np.float16)
    x_RI = x_RI.astype(np.float16)
    y_RI = y_RI.astype(np.float16)
    s_RI = s_RI.astype(np.float16)
    print("Channel matrix in (Re, Im) format:\n", H_RI)
    print("Hermitian matrix in (Re, Im) format:\n", G_RI)
    print("Cholesky dec. in (Re, Im) format:\n", L_RI)
    print("Input vector in (Re, Im) format:\n", b_RI)
    print("Output vector in (Re, Im) format:\n", x_RI)


    kwargs = {'name': 'mimo_mmse_f16', 'H': H_RI, 'G': G_RI, 'L' : L_RI, 'b' : b_RI, 'x' : x_RI, 'y' : y_RI, 's' : s_RI, 'N_tx' : N_tx, 'N_rx' : N_rx}
    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()
