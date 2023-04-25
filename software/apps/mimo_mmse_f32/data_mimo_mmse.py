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


def gen_input_data(N_rx, N_tx):

    # Create channel matrix
    H = np.random.rand(N_rx, N_tx).astype(np.float32) + 1.j * np.random.rand(N_rx, N_tx).astype(np.float32)
    # Create input vector
    b = np.random.rand(N_rx).astype(np.float32) + 1.j * np.random.rand(N_rx).astype(np.float32)
    # Generate noise variance
    sigma = np.diag(np.random.rand(N_tx, N_tx).astype(np.float32))

    # Matrix to be inverted in MMSE estimator
    H_h = np.asmatrix(H).H

    G = H_h * H
    print(sigma)
    G = G + np.diag(sigma)
    # Cholesky decomposition
    L = np.linalg.cholesky(G)
    # Linear system solution
    s = np.transpose(np.dot(H_h, b))
    y = solve_triangular(L, s, lower=True)
    x = solve_triangular(np.asmatrix(L).H, y)

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

    sigma = sigma.astype(np.float32)
    H_RI = H_RI.astype(np.float32)
    G_RI = G_RI.astype(np.float32)
    L_RI = L_RI.astype(np.float32)
    b_RI = b_RI.astype(np.float32)
    x_RI = x_RI.astype(np.float32)
    y_RI = y_RI.astype(np.float32)
    s_RI = s_RI.astype(np.float32)
    # print("Channel matrix in (Re, Im) format:\n", H_RI)
    # print("Hermitian matrix in (Re, Im) format:\n", G_RI)
    # print("Cholesky dec. in (Re, Im) format:\n", L_RI)
    # print("Input vector in (Re, Im) format:\n", b_RI)
    # print("Output vector in (Re, Im) format:\n", x_RI)

    return sigma, H_RI, G_RI, b_RI, x_RI


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
        default=pathlib.Path.cwd() / "data_mimo_mmse.h.tpl",
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
        help='Second dimension.'
    )
    parser.add_argument(
        "-k",
        "--iterations",
        type=int,
        required=False,
        default=256,
        help='Iterations.'
    )

    args = parser.parse_args()
    N_tx=args.transmitters
    N_rx=args.receivers
    itr=args.iterations

    sigma = np.zeros([itr, N_tx])
    H_RI = np.zeros([itr, 2*N_tx*N_rx])
    G_RI = np.zeros([itr, 2*N_tx*N_tx])
    b_RI = np.zeros([itr, 2*N_rx])
    x_RI = np.zeros([itr, 2*N_tx])
    for k in range(itr):
        sigma[k,:], H_RI[k,:], G_RI[k,:], b_RI[k,:], x_RI[k,:] = gen_input_data(N_rx, N_tx)

    sigma = np.reshape(sigma, (N_tx*itr))
    H_RI = np.reshape(H_RI, (2*N_rx*N_tx*itr))
    G_RI = np.reshape(G_RI, (2*N_tx*N_tx*itr))
    b_RI = np.reshape(b_RI, (2*N_rx*itr))
    x_RI = np.reshape(x_RI, (2*N_tx*itr))


    kwargs = {'name': 'mimo_mmse_f32', 'H': H_RI, 'G': G_RI, 'sigma': sigma, 'b' : b_RI, 'x' : x_RI, 'N_tx' : N_tx, 'N_rx' : N_rx, 'N_itr' : itr}
    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()
