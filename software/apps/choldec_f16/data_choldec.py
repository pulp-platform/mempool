#!/usr/bin/env python3

import numpy as np
import argparse
import pathlib
from scipy.linalg import solve_triangular
from mako.template import Template


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
        default=pathlib.Path.cwd() / "data_axb.h.tpl",
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
        default=4,
        help='First dimension.'
    )

    args = parser.parse_args()
    N_tx=args.transmitters
    N_rx=args.receivers

    # Create hermitian matrix
    H = np.random.rand(N_rx, N_tx) + 1.j * np.random.rand(N_tx, N_rx)
    # Matrix to be inverted
    G = H*(np.asmatrix(H).H)
    # Cholesky decomposition
    L = np.linalg.cholesky(G)

    G = np.reshape(G, (N_tx*N_rx, -1), order='C')
    L = np.reshape(L, (N_tx*N_rx, -1), order='C')
    G_RI = np.zeros(2*N_tx*N_rx)
    L_RI = np.zeros(2*N_tx*N_rx)

    for i in range(N_tx*N_rx):
        G_RI[2*i]   = G[i].real
        G_RI[2*i+1] = G[i].imag
        L_RI[2*i]   = L[i].real
        L_RI[2*i+1] = L[i].imag

    G_RI = G_RI.astype(np.float16)
    L_RI = L_RI.astype(np.float16)
    print("Input matrix in (Re, Im) format:\n",  G_RI)
    print("Output matrix in (Re, Im) format:\n", L_RI)


    kwargs = {'name': 'choldec_f16', 'G': G_RI, 'L' : L_RI, 'N_tx' : N_tx, 'N_rx' : N_rx}
    gen_data_header_file(args.outdir, args.tpl, **kwargs)

if __name__ == "__main__":
    main()
