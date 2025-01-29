#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Runs and end to end MIMO transmission with HW in the loop.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import scipy as sc
import pandas as pd
import time
import re
import argparse
import subprocess
import pathlib
import os
import sys
import shutil
import pyflexfloat as ff
import matplotlib.pyplot as plt
from concurrent.futures import ThreadPoolExecutor, wait

import qmath
import fmath

# __  __ ___ __  __  ___     _______  __
# |  \/  |_ _|  \/  |/ _ \ __|_   _\ \/ /
# | |\/| || || |\/| | (_) |___|| |  >  <
# |_|  |_|___|_|  |_|\___/     |_| /_/\_\
##


class Constellation:
    def __init__(self, constellation_type):
        self.constellation_type = constellation_type
        self.symbols = None
        self.codes = None
        self.num_bits = None
        self.get_constellation()

    def get_constellation(self):
        if self.constellation_type == '4QAM':
            self.symbols = np.array([-1 - 1j, +1 - 1j,
                                     -1 + 1j, +1 + 1j])
        elif self.constellation_type == '16QAM':
            self.symbols = np.array([-3 - 3j, -3 - 1j, -3 + 3j, -3 + 1j,
                                     -1 - 3j, -1 - 1j, -1 + 3j, -1 + 1j,
                                     +3 - 3j, +3 - 1j, +3 + 3j, +3 + 1j,
                                     +1 - 3j, +1 - 1j, +1 + 3j, +1 + 1j])
        elif self.constellation_type == '64QAM':
            self.symbols = np.array([-7 - 7j, -7 - 5j, -7 - 1j, -7 - 3j, -7 + 7j, -7 + 5j, -7 + 1j, -7 + 3j,
                                     -5 - 7j, -5 - 5j, -5 - 1j, -5 - 3j, -5 + 7j, -5 + 5j, -5 + 1j, -5 + 3j,
                                     -1 - 7j, -1 - 5j, -1 - 1j, -1 - 3j, -1 + 7j, -1 + 5j, -1 + 1j, -1 + 3j,
                                     -3 - 7j, -3 - 5j, -3 - 1j, -3 - 3j, -3 + 7j, -3 + 5j, -3 + 1j, -3 + 3j,
                                     +7 - 7j, +7 - 5j, +7 - 1j, +7 - 3j, +7 + 7j, +7 + 5j, +7 + 1j, +7 + 3j,
                                     +5 - 7j, +5 - 5j, +5 - 1j, +5 - 3j, +5 + 7j, +5 + 5j, +5 + 1j, +5 + 3j,
                                     +1 - 7j, +1 - 5j, +1 - 1j, +1 - 3j, +1 + 7j, +1 + 5j, +1 + 1j, +1 + 3j,
                                     +3 - 7j, +3 - 5j, +3 - 1j, +3 - 3j, +3 + 7j, +3 + 5j, +3 + 1j, +3 + 3j])
        else:
            raise ValueError("Unsupported constellation type.")

        # Calculate number of points and bits per symbol
        num_points = len(self.symbols)
        self.num_bits = np.int32(np.log2(num_points))

        # Generate binary codes for each constellation point
        self.codes = [format(i, f'0{self.num_bits}b')
                      for i in range(num_points)]

    def plot_constellation(self):
        # Plot the constellation
        plt.figure(figsize=(6, 6))
        plt.scatter(np.real(self.symbols), np.imag(self.symbols), color='blue')

        # Add labels (binary codes) to each point
        for i, point in enumerate(self.symbols):
            plt.text(
                np.real(point) + 0.1,
                np.imag(point) + 0.1,
                self.codes[i],
                fontsize=12)

        # Draw axes and grid
        plt.axhline(0, color='black', linewidth=0.5)
        plt.axvline(0, color='black', linewidth=0.5)
        plt.grid(True)

        # Label the axes
        plt.title('{} Constellation Diagram with Binary Labels'.format(
            self.constellation_type))
        plt.xlabel("In-phase (I)")
        plt.ylabel("Quadrature (Q)")

        # Save the plot as an image
        plt.savefig('MMSE_QAM.png')

        # Show the plot
        plt.show()

    def encode_symbol(self, x):
        # Combine real and imaginary parts into complex numbers
        x_complex = x[:, 0] + 1j * x[:, 1]
        # Find the closest symbols in the constellation
        idx_x = [np.argmin(np.abs(self.symbols - est)) for est in x_complex]
        # Get the corresponding binary code for each symbol
        bit_x = [self.codes[k] for k in idx_x]

        return bit_x


def mimo_transmission(
        N_tx, N_rx, N_itr, const, channel_type, SNRdB):

    # Create input vector
    symbols = const.symbols
    idx = np.random.randint(0, len(symbols), size=N_tx)
    Es = np.mean(abs(symbols)**2)
    x = symbols[idx]

    # Generate channel and noise
    if channel_type == 'rayleigh':
        # Generate Rayleigh fading channel
        H = np.sqrt(np.random.chisquare(2, [N_rx, N_tx])) + 1j * \
            np.sqrt(np.random.chisquare(2, [N_rx, N_tx]))
        Eh = (np.linalg.norm(H, 'fro')**2) / N_rx
    elif channel_type == 'random':
        H = np.sqrt(0.5) * \
            (np.random.normal(0, 1, [N_rx, N_tx]) + 1j *
             np.random.normal(0, 1, [N_rx, N_tx]))
        Eh = (np.linalg.norm(H, 'fro')**2) / N_rx
    else:
        # Generate AWGN channel
        H = np.eye(N_rx) + 1.j * np.zeros([N_rx, N_tx])
        Eh = 1

    # Noise variance
    Eb = Es / const.num_bits
    N = 0.5 * Es * 10**(-SNRdB / 10)
    n = (np.random.normal(0, np.sqrt(N), N_rx) + 1j *
         np.random.normal(0, np.sqrt(N), N_rx))
    N = N / (Es * Eh)

    # Channel propagation
    y = np.dot(H, x) + n.flatten()

    return {"x": x, "N": N, "y": y, "H": H}


def fmmse(x, H, y, N, my_type):

    # Type cast
    H = H.real.astype(my_type) + 1j * H.imag.astype(my_type)
    x = x.real.astype(my_type) + 1j * x.imag.astype(my_type)
    y = y.real.astype(my_type) + 1j * y.imag.astype(my_type)
    N = N.astype(my_type)

    # MMSE estimator
    H_h = H.conj().T
    G = np.matmul(H_h, H) + N * np.eye(H.shape[1])
    y1 = np.dot(H_h, y)
    xhat = np.matmul(np.linalg.inv(G), y1)
#    L = fmath.fcholesky(G)
#    y2 = fmath.finvertLt(L, y1)
#    xhat = fmath.finvertUt(np.asmatrix(L).H, y2)
    # Type cast
    xhat = xhat.real.astype(my_type) + 1j * xhat.imag.astype(my_type)

    N = np.ones(2 * H.shape[1]) * N
    H = H.flatten(order='C')
    H = np.column_stack((H.real, H.imag)).flatten()
    x = np.column_stack((x.real, x.imag)).flatten()
    y = np.column_stack((y.real, y.imag)).flatten()
    xhat = np.column_stack((xhat.real, xhat.imag)).flatten()

    return {"H": H, "x": x, "y": y, "N": N, "xhat" : xhat}


def qmmse(x, H, y, N, my_type):

    # Type cast
    if my_type == np.int32:
        fp = 16
    elif my_type ==  np.int16:
        fp = 8
    SCALE_FACTOR = 2**fp

    # Normalize inputs according to float computation
    G = np.matmul(H.conj().T, H) + N * np.eye(H.shape[1])
    y1 = np.dot(H.conj().T, y)
    H_max = max(np.abs(H.real).max(), np.abs(H.imag).max())
    G_max = max(np.abs(G.real).max(), np.abs(G.imag).max())
    N_max = max(np.abs(N.real).max(), np.abs(N.imag).max())
    y_max = max(np.abs(y.real).max(), np.abs(y.imag).max())
    y1_max = max(np.abs(y1.real).max(), np.abs(y1.imag).max())
    MAX = max(H_max, G_max, N_max, y_max)

    rH = np.round((H.real / MAX) * SCALE_FACTOR).astype(int)
    iH = np.round((H.imag / MAX) * SCALE_FACTOR).astype(int)
    ry = np.round((y.real / MAX) * SCALE_FACTOR).astype(int)
    iy = np.round((y.imag / MAX) * SCALE_FACTOR).astype(int)
    rN = np.round((N.real / MAX) * SCALE_FACTOR).astype(int)
    iN = np.round((N.imag / MAX) * SCALE_FACTOR).astype(int)

    # Hermitian
    rG, iG = qmath.qcmatmul(np.transpose(rH), -np.transpose(iH), rH, iH, fp, my_type)
    np.fill_diagonal(rG, rG.diagonal() + rN)
    ry1, iy1 = qmath.qcmvmul(np.transpose(rH), -np.transpose(iH), ry, iy, fp, my_type)
    # Solve linear system
    rL, iL = qmath.qcholesky(rG, iG, fp, my_type)
    ry2, iy2 = qmath.qinvertLt(rL, iL, ry1, iy1, fp, my_type)
    rx, ix = qmath.qinvertUt(np.transpose(rL), -np.transpose(iL), ry2, iy2, fp, my_type)
    N = np.ones(2 * H.shape[1]) * rN

    # For result checking
    xhat = qmath.from_fixed_point(rx, ix, fp, np.int16)
    xhat = np.column_stack((xhat.real, xhat.imag)).flatten()
    # For execution on Banshee
    H = np.column_stack((rH, iH)).flatten()
    y = np.column_stack((ry, iy)).flatten()
    return {"H": H, "y": y, "N": N, "xhat" : xhat}

# ___               _
# | _ ) __ _ _ _  __| |_  ___ ___
# | _ \/ _` | ' \(_-< ' \/ -_) -_)
# |___/\__,_|_||_/__/_||_\___\___|
##

class Banshee:
    def __init__(self, mempool_dir, banshee_dir, compiler_flag: str, H, N, y, N_tx, N_rx, N_itr, precision: str = "8b-MP", num_executors: int = 1):

        # Directories (assuming these are passed as arguments or set beforehand)
        self.MEMPOOL_DIR = mempool_dir
        self.BANSHEE_DIR = banshee_dir
        self.SW_DIR = mempool_dir / "software/apps/baremetal"
        self.DATA_DIR = mempool_dir / "software/data"
        self.BIN_DIR = mempool_dir / "software/bin/apps/baremetal"

        # Initialize the necessary instance variables
        self.compiler_flag = compiler_flag
        self.precision = precision
        self.num_executors = num_executors

        # Initialize input variables
        self.N_tx = N_tx
        self.N_rx = N_rx
        self.N_itr = N_itr

        # Set app and datatype based on precision
        if precision in ('f08_zfinx', 'f08_wDotp'):
            self.H = ff.array(H, "e5m2")
            self.N = ff.array(N, "e5m2")
            self.y = ff.array(y, "e5m2")
            self.app = "mimo_mmse_f8"
            self.datatype = "__fp8"
        else:
            self.H = H
            self.N = N
            self.y = y
            self.app = "mimo_mmse_f16"
            self.datatype = "__fp16"

    def stringify_array(self, arr, typ, name):
        """ Generates a string for array initialization in C from a numpy input. """

        count = 0
        output_string = typ
        output_string += " __attribute__((aligned(sizeof(int32_t)), section(\".l2\"))) "
        output_string += name + '[{}] = {{\n'.format(arr.size)
        for value in arr:
            if typ == '__fp16':
                output_string += '({}){:0.5f}f, '.format(typ, value)
            elif typ == '__fp8':
                output_string += '(__fp8)' + f'{hex(value.bits())}' + ', '
            count += 1
            if count % 8 == 0:
                output_string += '\n'
        output_string = output_string[:-3]
        output_string += "};\n"
        return output_string

    def gen_data_header_file(self, datadir, **kwargs):
        """ Creates data.h file for the application to be compiled. """

        file = datadir / f"data_{self.app}.h"
        string = "// Copyright 2022 ETH Zurich and University of Bologna.\n \
                  // Licensed under the Apache License, Version 2.0, see LICENSE for details.\n \
                  // SPDX-License-Identifier: Apache-2.0\n\n \
                  // File generated with .data/print_header.py\n"
        string += "#define N_TX ({})\n".format(self.N_tx)
        string += "#define N_RX ({})\n".format(self.N_rx)
        string += "#define N_ITR ({})\n".format(kwargs['N_itr'])
        string += self.stringify_array(kwargs['H'].flatten(order='F'), self.datatype, "l2_H")
        string += self.stringify_array(kwargs['y'].flatten(order='F'), self.datatype, "l2_y")
        string += self.stringify_array(kwargs['N'].flatten(order='F'), self.datatype, "l2_S")
        with open(file, 'w') as f:
            f.write(string)

    def compile_app(self, datadir, bindir):
        """ Compiles the application using MemPool runtime """

        compile_app = f"DEFINES={self.compiler_flag} "
        compile_app += f"DATA_DIR={datadir} "
        compile_app += f"BIN_DIR={bindir} "
        compile_app += "l1_bank_size=16384 config=terapool "
        compile_app += f"make COMPILER=llvm "
        compile_app += f"{self.app} -C {self.SW_DIR}"
        # Compile code
        compiled = subprocess.run(compile_app, shell=True, capture_output=True)
        if compiled.returncode != 0:
            # Print error message
            print(f"Error occurred during compilation:\n{compiled.stderr}", file=sys.stderr)
            # Exit the program with a non-zero exit code
            sys.exit(compiled.returncode)
        return compiled.stdout

    def run_banshee(self, bindir):
        """ Runs application on Banshee """

        banshee_arg = " --num-cores 1 --num-clusters 1 --configuration config/terapool.yaml"
        banshee_app = f" {bindir}/{self.app}"
        run_banshee = f"SNITCH_LOG=info cargo run --{banshee_arg}{banshee_app}"
        # Run Banshee
        os.chdir(self.BANSHEE_DIR)
        file_dir = os.path.dirname(os.path.realpath(__file__))
        result = subprocess.run(
            run_banshee,
            shell=True,
            capture_output=True,
            text=True
        )
        os.chdir(file_dir)
        return result.stderr

    def banshee_cast_output(self, string):
        # Capture the output
        pattern = r"RES=[0-9a-fA-F]{4}"
        matches = re.findall(pattern, string)
        half_float_array = []
        for match in matches:
            hex_str = match[-4:]  # Get the hex number part
            hex_int = np.uint16(int(hex_str, 16))
            half_float = np.frombuffer(hex_int.tobytes(), dtype=np.float16)[0]
            half_float_array.append(half_float)
        return np.array(half_float_array)


    def banshee_call(self):
        """ Parallelized banshee call """

        # Split H, N, y across executors
        H_split = np.array_split(self.H, self.num_executors, axis=1)
        N_split = np.array_split(self.N, self.num_executors, axis=1)
        y_split = np.array_split(self.y, self.num_executors, axis=1)
        N_itr = self.N_itr // self.num_executors

        results = []
        with ThreadPoolExecutor(max_workers=self.num_executors) as executor:

            for i in range(self.num_executors):
                # Define the specific output directory for each executor
                datadir = self.DATA_DIR / f"data{i}"
                bindir = self.BIN_DIR / f"bin{i}"
                datadir.mkdir(parents=True, exist_ok=True)
                bindir.mkdir(parents=True, exist_ok=True)
                self.gen_data_header_file(datadir=datadir,
                    H=H_split[i], N=N_split[i], y=y_split[i], N_itr=N_itr)
                self.compile_app(datadir=datadir, bindir=bindir)

            futures = []
            for i in range(self.num_executors):
                bindir = self.BIN_DIR / f"bin{i}"
                # Generate data header file concurrently
                futures.append(executor.submit(
                    self.run_banshee,
                    bindir=bindir,
                ))
            wait(futures)
            shutil.rmtree(datadir)
            shutil.rmtree(bindir)

            for future in futures:
                try:
                    result = future.result()
                    if isinstance(result, str):  # Only process run_banshee output
                        results.append(self.banshee_cast_output(result))
                except Exception as e:
                    print(f"An error occurred: {e}", file=sys.stderr)

        # Aggregate all results from banshee_cast_output into a single numpy vector
        final_result = np.concatenate(results) if results else np.array([])
        return final_result

def plot_result(vBER, vEVM, vSNRdB, precisions):

    # Create a figure with two subplots side by side
    fig, axs = plt.subplots(1, 2, figsize=(16, 6))

    # Plot BER vs SNR in the first subplot
    for j in range(len(vBER)):
        axs[0].semilogy(vSNRdB, vBER[j],
                        marker='o', label='{}'.format(precisions[j][0]))
    axs[0].set_title('BER vs SNR')
    axs[0].set_xlabel('SNR (dB)')
    axs[0].set_ylabel('BER')
    axs[0].grid(True, which='both')
    axs[0].legend()

    # Plot EVM vs SNR in the second subplot
    for j in range(len(vEVM)):
        axs[1].plot(vSNRdB, vEVM[j],
                    marker='o', label='{}'.format(precisions[j][0]))
    axs[1].set_title('EVM vs SNR')
    axs[1].set_xlabel('SNR (dB)')
    axs[1].set_ylabel('EVM')
    axs[1].grid(True, which='both')
    axs[1].legend()
    # Adjust layout and show the plots
    plt.tight_layout()
    plt.savefig('MMSE_BER.png')


def main():

    run_banshee = 1

    # Create an argument parser for the PHY simulator
    parser = argparse.ArgumentParser(description='Simulator for lower PHY')

    # Directory arguments
    # -----------------------------------------------------------
    # Set the project root directory, software directory, data directory, and toolchain path
    script_dir = pathlib.Path(__file__).resolve()  # Get the absolute path of the current script
    parser.add_argument("--rootdir", type=pathlib.Path,
                        default=script_dir.parents[2],  # Two levels above current script
                        required=False,
                        help='Root directory of the project. Defaults to two levels above the script location.')
    parser.add_argument("--bansheedir", type=pathlib.Path,
                        default=script_dir.parents[2] / "toolchain" / "banshee",
                        required=False,
                        help='Directory for Banshee toolchain, relative to the project root.')
    parser.add_argument("--threads", type=int, default=1, required=False,
                        help='Number of parallel threads for Banshee iterations.')

    # Transmission parameters
    # -----------------------------------------------------------
    # Configure simulation parameters such as constellation, channel type, number of UEs, antennas, and batch size
    parser.add_argument("-s", "--constellation", type=str, default="16QAM", required=False,
                        help='Transmission constellation type. Defaults to "16QAM".')
    parser.add_argument("-c", "--channel", type=str, default="awgn", required=False,
                        help='Type of transmission channel. Defaults to "awgn".')
    parser.add_argument("-n", "--transmitters", type=int, default=4, required=False,
                        help='Number of transmitting user equipments (UEs). Defaults to 4.')
    parser.add_argument("-m", "--receivers", type=int, default=4, required=False,
                        help='Number of receiving antennas. Defaults to 4.')
    parser.add_argument("-b", "--iterations", type=int, default=500, required=False,
                        help='Batch size for transmission processing that fits within L1 cache. Defaults to 500.')

    args = parser.parse_args()
    # Parameters
    channel_type = args.channel
    N_tx         = args.transmitters
    N_rx         = args.receivers
    N_itr        = args.iterations

    # Arithmetic precisions + compiler flags
    if run_banshee & (channel_type == "rayleigh"):
        precisions = [['f64', ""],
                      ['f16_zfinx', "\"-DSINGLE -DBANSHEE\""],
                      ['f16_cDotp', "\"-DSINGLE -DBANSHEE -DVEC -D__CDOTP\""]]
        vSNRdB = range(0, 20, 2)
    elif run_banshee & (channel_type == "awgn"):
        precisions = [['f64', ""],
                      ['f16_zfinx', "\"-DSINGLE -DBANSHEE\""],
                      ['f16_wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""],
                      ['f16_cDotp', "\"-DSINGLE -DBANSHEE -DVEC -D__CDOTP\""]]
        vSNRdB = range(0, 20, 2)
    else:
        precisions = [['f64', ''],
                      ['f16', ''],
                      ['q16', '']]
        vSNRdB = range(0, 20, 2)

    # Constellation
    const = Constellation(args.constellation)

    # Vectors for computation
    vTBE = np.zeros([len(precisions), len(vSNRdB)], np.float64)
    vBER = np.zeros([len(precisions), len(vSNRdB)], np.float64)
    vMSE = np.zeros([len(precisions), len(vSNRdB)], np.float64)
    vEVM = np.zeros([len(precisions), len(vSNRdB)], np.float64)
    vVM = np.zeros(len(vSNRdB), np.float64)


    # -----------------------------------------------------------
    # SNR LOOP
    # -----------------------------------------------------------

    startime = time.time()
    # Loop over the SNRs
    for iSNR in range(0, len(vSNRdB)):

        SNRdB = vSNRdB[iSNR]
        vxhat = np.empty((len(precisions), 2 * N_tx, N_itr), dtype=np.float64)

        # -----------------------------------------------------------
        # MC-iterations
        # -----------------------------------------------------------

        # Golden model
        vxf64 = np.empty((2 * N_tx, N_itr), dtype=np.float64)
        # f16 inputs to Banshee simulation
        vNf16 = np.empty((2 * N_tx, N_itr), dtype=np.float16)
        vyf16 = np.empty((2 * N_rx, N_itr), dtype=np.float16)
        vHf16 = np.empty((2 * N_tx * N_rx, N_itr), dtype=np.float16)
        # q16 inputs to Banshee simulation
        vNq16 = np.empty((2 * N_tx, N_itr), dtype=np.int16)
        vyq16 = np.empty((2 * N_rx, N_itr), dtype=np.int16)
        vHq16 = np.empty((2 * N_tx * N_rx, N_itr), dtype=np.int16)

        np.random.seed(int(time.time()))
        for iMC in range(0, N_itr):

            tx = mimo_transmission(N_tx, N_rx, N_itr, const, channel_type, SNRdB)
            rf64 = fmmse(tx["x"], tx["H"], tx["y"], tx["N"], np.float64)
            rf16 = fmmse(tx["x"], tx["H"], tx["y"], tx["N"], np.float16)
            vxhat[0, :, iMC] = rf64["xhat"]
            vxhat[1, :, iMC] = rf16["xhat"]
            # Golden model
            vxf64[:, iMC] = rf64["x"]
            # f16 inputs to Banshee simulation
            vHf16[:, iMC] = rf16["H"]
            vyf16[:, iMC] = rf16["y"]
            vNf16[:, iMC] = rf16["N"]

#            rq16 = qmmse(tx["x"], tx["H"], tx["y"], tx["N"], np.int16)
#            vxhat[2, :, iMC] = rq16["xhat"]
#            # q16 inputs to Banshee simulation
#            vHq16[:, iMC] = rq16["H"]
#            vyq16[:, iMC] = rq16["y"]
#            vNq16[:, iMC] = rq16["N"]

        # ----------------------------------------------------------------
        # BANSHEE CALL
        # ----------------------------------------------------------------
        if run_banshee:
            for iPrec, (precision, flag) in enumerate(precisions[1:]):
                banshee = Banshee(
                    mempool_dir=args.rootdir, banshee_dir=args.bansheedir,
                    compiler_flag=flag, precision=precision,
                    num_executors=args.threads,
                    H=vHf16, N=vNf16, y=vyf16,
                    N_tx=N_tx, N_rx=N_rx, N_itr=N_itr
                )
                result = banshee.banshee_call()
                vxhat[iPrec + 1, :, :] = result.reshape(2 * N_tx, N_itr, order='F')

        # ----------------------------------------------------------------

        # ----------------------------------------------------------------
        # BER COMPUTATION
        # ----------------------------------------------------------------
        for iMC in range(0, N_itr):
            # Compute bit-encodings for x
            x = (vxf64[:, iMC]).reshape(-1, 2)
            bit_x = const.encode_symbol(x)
            vVM[iSNR] += np.linalg.norm(x)**2
            # Compute bit-encodings for xhat
            for iPrec in range(0, len(precisions)):
                xhat = (vxhat[iPrec, :, iMC]).reshape(-1, 2)
                bit_xhat = const.encode_symbol(xhat)
                # Compute BER between x and each xhat in vvxhat
                vTBE[iPrec][iSNR] += sum(a_bit != b_bit
                                         for a_str, b_str in zip(bit_x, bit_xhat)
                                         for a_bit, b_bit in zip(a_str, b_str))
                # Compute MSE between x and each xhat in vvxhat
                vMSE[iPrec][iSNR] += np.linalg.norm(xhat - x)**2
        # ----------------------------------------------------------------

        # -----------------------------------------------------------
        # END BATCH LOOP
        # -----------------------------------------------------------

        # Print results at checkpoint
        elapstime = time.strftime("%Hh%Mm%Ss",
                                  time.gmtime(time.time() - startime))
        checkpoint_print = elapstime + \
            " SNR={}dB BER@{}itr= ".format(SNRdB, N_itr)
        total_bits = (N_tx * const.num_bits * N_itr)
        for iPrec in range(len(vTBE)):
            checkpoint_print += "{:.4f}, ".format(vTBE[iPrec][iSNR] / total_bits)
            vBER[iPrec][iSNR] = vTBE[iPrec][iSNR] / total_bits
            vEVM[iPrec][iSNR] = np.sqrt(vMSE[iPrec][iSNR] / vVM[iSNR])
        print(checkpoint_print)

    # -----------------------------------------------------------
    # END SNR LOOP
    # -----------------------------------------------------------

    # Store output in file
    current_local_time = time.localtime()
    timestr = time.strftime("%Y%m%d_%H%M%S", current_local_time)
    col_names = [precision[0] for precision in precisions]
    row_names = [f"{value} dB" for value in vSNRdB]
    df_ber = pd.DataFrame(np.transpose(vBER), columns=col_names, index=row_names)
    df_evm = pd.DataFrame(np.transpose(vEVM), columns=col_names, index=row_names)
    #df_ber.to_excel(f"BER_{timestr}.ods", index=True, header=True, engine='odf')
    #df_evm.to_excel(f"EVM_{timestr}.ods", index=True, header=True, engine='odf')


    # Plot output
    plot_result(vBER, vEVM, vSNRdB, precisions)
    const.plot_constellation()


if __name__ == "__main__":
    main()
