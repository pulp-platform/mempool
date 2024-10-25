#!/usr/bin/env python3

# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Runs and end to end MIMO transmission with HW in the loop.
# Author: Marco Bertuletti <mbertuletti@iis.ee.ethz.ch>

import numpy as np
import pandas as pd
import time
import re
import argparse
import subprocess
import pathlib
import os
import sys
import pyflexfloat as ff
import matplotlib.pyplot as plt
from scipy.linalg import solve_triangular


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


def mmse(x, H, y, N, my_type):

    # Type cast
    H = H.real.astype(my_type) + 1j * H.imag.astype(my_type)
    x = x.real.astype(my_type) + 1j * x.imag.astype(my_type)
    y = y.real.astype(my_type) + 1j * y.imag.astype(my_type)
    N = N.astype(my_type)

    # MMSE estimator
    H_h = H.conj().T
    G = np.matmul(H_h, H) + N * np.eye(H.shape[1])
    xhat = np.matmul(np.linalg.inv(G), np.dot(H_h, y))
    # Type cast
    xhat = xhat.real.astype(my_type) + 1j * xhat.imag.astype(my_type)
    H = H.flatten(order='C')
    return N, H, y, x, xhat


def generate_mimo_transmission_f16(
        N_tx, N_rx, N_itr, symbols, channel_type, SNRdB):

    # Create input vector
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
    N = 0.5 * Es * Eh * 10**(-SNRdB / 10)
    n = (np.random.normal(0, np.sqrt(N), N_rx) + 1j *
         np.random.normal(0, np.sqrt(N), N_rx))
    N = N / Es

    # Channel propagation
    y = np.dot(H, x) + n.flatten()
    # MMSE estimator
    N64, H64, y64, x64, xhat64 = mmse(x, H, y, N, np.float64)
    N16, H16, y16, x16, xhat16 = mmse(x, H, y, N, np.float16)

    # 16b inputs and outputs
    N16 = N16 * np.ones(2 * N_tx)
    y16 = np.column_stack((y16.real, y16.imag)).flatten()
    H16 = np.column_stack((H16.real, H16.imag)).flatten()
    x16 = np.column_stack((x16.real, x16.imag)).flatten()
    xhat16 = np.column_stack((xhat16.real, xhat16.imag)).flatten()
    # Golden model
    x64 = np.column_stack((x64.real, x64.imag)).flatten()
    xhat64 = np.column_stack((xhat64.real, xhat64.imag)).flatten()

    output = {
        "N16": N16,
        "y16": y16,
        "H16": H16,
        "x16": x16,
        "x64": x64,
        "xhat16": xhat16,
        "xhat64": xhat64
    }
    return output


# ___               _
# | _ ) __ _ _ _  __| |_  ___ ___
# | _ \/ _` | ' \(_-< ' \/ -_) -_)
# |___/\__,_|_||_/__/_||_\___\___|
##


def stringify_array(arr, typ, name):
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


def gen_data_header_file(outdir, my_type, **kwargs):

    file = outdir / f"{kwargs['name']}.h"
    string = "// Copyright 2022 ETH Zurich and University of Bologna.\n \
              // Licensed under the Apache License, Version 2.0, see LICENSE for details.\n \
              // SPDX-License-Identifier: Apache-2.0\n\n \
              // File generated with .data/print_header.py\n"
    with open(file, 'w') as f:
        string += "#define N_TX ({})\n".format(kwargs['N_tx'])
        string += "#define N_RX ({})\n".format(kwargs['N_rx'])
        string += "#define N_ITR ({})\n".format(kwargs['N_itr'])
        string += stringify_array(kwargs['H'].flatten(order='F'),
                                  my_type, "l2_H")
        string += stringify_array(kwargs['y'].flatten(order='F'), my_type, "l2_y")
        string += stringify_array(kwargs['N'].flatten(order='F'), my_type, "l2_S")
        f.write(string)


def banshee_call(banshee_dir: pathlib.Path.cwd(),
                 software_dir: pathlib.Path.cwd(),
                 compiler_flag: "",
                 app: "mimo_mmse_f16"):

    os.chdir(banshee_dir)
    file_dir = os.path.dirname(os.path.realpath(__file__))
    compile_app = "DEFINES=" + compiler_flag + " "
    compile_app += "l1_bank_size=16384 config=terapool "
    compile_app += "make COMPILER=llvm ".format(file_dir)
    compile_app += "{} -C {}/apps/baremetal".format(app, software_dir)
    banshee_arg = " --num-cores 1 --num-clusters 1 --configuration config/terapool.yaml"
    banshee_app = " {}/bin/apps/baremetal/{}".format(software_dir, app)
    run_banshee = "SNITCH_LOG=info cargo run --" + banshee_arg + banshee_app

    # Compile code
    compiled = subprocess.run(compile_app, shell=True, capture_output=True)
    if compiled.returncode != 0:
        # Print error message
        print(f"Error occurred:\n{compiled.stderr}", file=sys.stderr)
        # Exit the program with a non-zero exit code
        sys.exit(compiled.returncode)

    # Run Banshee
    result = subprocess.run(
        run_banshee,
        shell=True,
        capture_output=True,
        text=True)
    os.chdir(file_dir)

    return result


def banshee_cast_output(string):

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
    parser.add_argument("--swdir", type=pathlib.Path,
                        default=script_dir.parents[1],  # One level above current script
                        required=False,
                        help='Directory for software components, relative to the project root.')
    parser.add_argument("--datadir", type=pathlib.Path,
                        default=script_dir.parents[1] / "data",  # "../data"
                        required=False,
                        help='Directory for data files, relative to the project root.')
    parser.add_argument("--bansheedir", type=pathlib.Path,
                        default=script_dir.parents[2] / "toolchain" / "banshee",  # "../../toolchain/banshee"
                        required=False,
                        help='Directory for Banshee toolchain, relative to the project root.')
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
    parser.add_argument("-b", "--batchsize", type=int, default=500, required=False,
                        help='Batch size for transmission processing that fits within L1 cache. Defaults to 500.')

    args = parser.parse_args()
    # Directories
    MEMPOOL_DIR  = args.rootdir
    SOFTWARE_DIR = args.swdir
    DATA_DIR     = args.datadir
    BANSHEE_DIR  = args.bansheedir
    # Parameters
    channel_type = args.channel
    N_tx         = args.transmitters
    N_rx         = args.receivers
    N_batch      = args.batchsize

    # Arithmetic precisions + compiler flags
    if run_banshee & (channel_type == "rayleigh"):
        precisions = [['64b', ""],
                      ['16b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""],
                      ['16b-MP cDotp', "\"-DSINGLE -DBANSHEE -DVEC -D__CDOTP\""]]
        vSNRdB = range(0, 40, 4)
        vITR = np.concatenate([np.full(9, 1), np.full(1, 2)])
    elif run_banshee & (channel_type == "awgn"):
        precisions = [['64b', ""],
                      ['16b-MP', "\"-DSINGLE -DBANSHEE\""],
                      ['16b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""],
                      ['16b-MP cDotp', "\"-DSINGLE -DBANSHEE -DVEC -D__CDOTP\""],
                      ['8b-MP', "\"-DSINGLE -DBANSHEE\""],
                      ['8b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""]]
        vSNRdB = range(0, 20, 2)
        vITR = np.concatenate([np.full(3, 1), np.full(5, 2), np.full(2, 6)])
    else:
        precisions = [['64b', '']]
        vSNRdB = range(0, 20, 2)
        vITR = np.concatenate([np.full(3, 1), np.full(5, 2), np.full(2, 6)])

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
        N_itr = vITR[iSNR] * N_batch

        # -----------------------------------------------------------
        # BATCH LOOP
        # -----------------------------------------------------------

        # Loop over the batches that fit the cluster L1 memory
        for iMC in range(0, N_itr, N_batch):

            # Vector for results
            vxhat = np.empty(
                (len(precisions), 2 * N_tx, N_batch), dtype=np.float64)

            # Generate data
            np.random.seed(int(time.time()))
            vN16 = np.empty((2 * N_tx, N_batch), dtype=np.float16)
            vy16 = np.empty((2 * N_rx, N_batch), dtype=np.float16)
            vH16 = np.empty((2 * N_tx * N_rx, N_batch), dtype=np.float16)
            vx16 = np.empty((2 * N_tx, N_batch), dtype=np.float16)
            vxhat16 = np.empty((2 * N_tx, N_batch), dtype=np.float16)
            # Golden model
            vx64 = np.empty((2 * N_tx, N_batch), dtype=np.float64)
            vxhat64 = np.empty((2 * N_tx, N_batch), dtype=np.float64)

            # Random BER iterations
            for iBatch in range(0, N_batch):
                output_mmse = generate_mimo_transmission_f16(
                    N_tx, N_rx, N_batch, const.symbols, channel_type, SNRdB)
                vN16[:, iBatch] = output_mmse["N16"]
                vy16[:, iBatch] = output_mmse["y16"]
                vH16[:, iBatch] = output_mmse["H16"]
                vx16[:, iBatch] = output_mmse["x16"]
                vx64[:, iBatch] = output_mmse["x64"]
                vxhat16[:, iBatch] = output_mmse["xhat16"]
                vxhat64[:, iBatch] = output_mmse["xhat64"]

            # Collect decoded symbols
            vxhat[0, :, :] = vxhat64

            # ----------------------------------------------------------------
            # BANSHEE CALL
            # ----------------------------------------------------------------
            if run_banshee:
                for iPrec, (precision, flag) in enumerate(precisions[1:]):
                    if precision in ('8b-MP', '8b-MP wDotp'):
                        vH8 = ff.array(vH16, "e5m2")
                        vN8 = ff.array(vN16, "e5m2")
                        vy8 = ff.array(vy16, "e5m2")
                        kwargs = {'name': 'data_mimo_mmse_f8',
                                  'H': vH8, 'N': vN8, 'y': vy8,
                                  'N_tx': N_tx, 'N_rx': N_rx, 'N_itr': N_batch}
                        gen_data_header_file(DATA_DIR, '__fp8', **kwargs)
                        result = banshee_call(
                            BANSHEE_DIR, SOFTWARE_DIR, flag, "mimo_mmse_f8")
                    else:
                        kwargs = {'name': 'data_mimo_mmse_f16',
                                  'H': vH16, 'N': vN16, 'y': vy16,
                                  'N_tx': N_tx, 'N_rx': N_rx, 'N_itr': N_batch}
                        gen_data_header_file(DATA_DIR, '__fp16', **kwargs)
                        result = banshee_call(
                            BANSHEE_DIR, SOFTWARE_DIR, flag, "mimo_mmse_f16")
                    result_casted = banshee_cast_output(result.stderr)
                    vxhat[iPrec + 1, :, :] = result_casted.reshape(2 * N_tx, N_batch, order='F')

            # ----------------------------------------------------------------

            # ----------------------------------------------------------------
            # BER COMPUTATION
            # ----------------------------------------------------------------
            for iBatch in range(0, N_batch):

                # Compute bit-encodings for x
                x = (vx64[:, iBatch]).reshape(-1, 2)
                bit_x = const.encode_symbol(x)
                vVM[iSNR] += np.linalg.norm(x)**2

                # Compute bit-encodings for xhat
                for iPrec in range(0, len(precisions)):
                    xhat = (vxhat[iPrec, :, iBatch]).reshape(-1, 2)
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
    df_ber.to_excel(f"BER_{timestr}.ods", index=True, header=True, engine='odf')
    df_evm.to_excel(f"EVM_{timestr}.ods", index=True, header=True, engine='odf')


    # Plot output
    plot_result(vBER, vEVM, vSNRdB, precisions)
    const.plot_constellation()


if __name__ == "__main__":
    main()
