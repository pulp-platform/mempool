# Copyright 2022 ETH Zurich and University of Bologna.
# Solderpad Hardware License, Version 0.51, see LICENSE for details.
# SPDX-License-Identifier: SHL-0.51

# Runs and end to end MIMO transmission with HW in the loop.
# Author: Mahdi Abdollahpour, University of Bologna

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
import end2end_mimo



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
    bb = kwargs['N_itr']
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


def plot_result(vBER, vEVM, vSNRdB, precisions, name_tag):

    # Create a figure with two subplots side by side
    fig, axs = plt.subplots(1, 2, figsize=(16, 6))

    # Plot BER vs SNR in the first subplot
    for j in range(len(vBER)):
        axs[0].semilogy(vSNRdB, vBER[j],
                        marker='o', label='{}'.format(precisions[j][0]))
    axs[0].set_title('BER vs SNR')
    # axs[0].set_xlabel('SNR (dB)')
    axs[0].set_xlabel('Eb/No (dB)')
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
    plt.savefig(f'MMSE_BER_{name_tag}.png')
    # plt.show()

def bits_per_symbol(mod_scheme):
    mod_scheme = mod_scheme.lower()
    mod_to_bits = {
        'bpsk': 1,
        'qpsk': 2,
        '16qam': 4,
        '64qam': 6,
        '256qam': 8
    }

    if mod_scheme in mod_to_bits:
        return mod_to_bits[mod_scheme]
    else:
        raise ValueError(f"Unknown modulation scheme: {mod_scheme}")

def cast_reshape_to_2D_real(data, dtype=np.float16):

    first_dim_size = data.shape[0]
    last_dim_size = data.shape[1]*2


    # stack as real float16 elements
    if np.isrealobj(data):
        data = np.stack( (  data.astype(dtype),data.astype(dtype)  ) ,axis=-1)
    else:
        data = np.stack( (  data.real.astype(dtype),data.imag.astype(dtype)  ) ,axis=-1)

    # reshape to 2D
    data = data.reshape(first_dim_size,last_dim_size)

    # swap batch dimension for banshee call (put the batch dimension in 1'th axis)
    data = np.transpose(data,(-1,0))

    return data

def cast_reshape_to_2D_complex(data,dtype=np.complex64):

    # [2*N_tx, batch_size(N_batch * num_symbols)]
    shape = data.shape
    data_size = int(shape[0]/2)
    batch_size = shape[1]

    # to [batch_size(N_batch * num_symbols), 2*N_tx]
    data = np.transpose(data,(1,0))

    # to [batch_size, data_size, 2]
    data = np.reshape(  data, (batch_size,data_size,2)  )

    # to complex [batch_size, data_size]
    data_complex = np.zeros((batch_size,data_size),dtype=dtype)
    data_complex.real = np.squeeze(data[:,:,0])
    data_complex.imag = np.squeeze(data[:,:,1])


    return data_complex



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
    parser.add_argument("-b", "--batchsize", type=int, default=32, required=False,
                        help='Batch size for transmission processing that fits within L1 cache. Defaults to 32.')
    parser.add_argument("-f", "--frequency", type=float, default=3.5e9, required=False,
                        help='Carrier frequency of the OFDM MIMO transmision. Defaults to 3.5 GHz')
    parser.add_argument("-t", "--fftsize", type=int, default=128, required=False,
                        help='Number of subcarriers. Default to 128')
    parser.add_argument("--numofdmsymbols", type=int, default=14, required=False,
                        help='Number of OFDM symbols. Default to 14')




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

    carrier_frequency = args.frequency
    fft_size = args.fftsize
    num_ofdm_symbols = args.numofdmsymbols


    num_symbols = num_ofdm_symbols * fft_size
   

    num_bits_per_symbol = bits_per_symbol(args.constellation)
    constellation = args.constellation


    # Arithmetic precisions + compiler flags
    if run_banshee & (channel_type == "rayleigh"):
        precisions = [['64b', ""],
                      ['16b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""]]
        vSNRdB = range(-6, 40, 4)
        vITR = np.concatenate([np.full(9, 1), np.full(1, 2)])
    elif run_banshee & (channel_type == "awgn"):
        precisions = [['64b', ""],
                      ['16b-MP', "\"-DSINGLE -DBANSHEE\""],
                      ['16b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""],
                      ['16b-MP cDotp', "\"-DSINGLE -DBANSHEE -DVEC -D__CDOTP\""],
                      ['8b-MP', "\"-DSINGLE -DBANSHEE\""],
                      ['8b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""]
                      ]
        vSNRdB = range(0, 14, 2)
        vITR = np.concatenate([np.full(3, 3), np.full(5, 6), np.full(5, 10)])
        max_it = 50
        be_target = 10
    elif run_banshee & (channel_type == "umi"):
        precisions = [['64b', ""],
                      # ['16b-MP', "\"-DSINGLE -DBANSHEE\""],
                      ['16b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""], #works
                      ['16b-MP wDotp dgLoaded', "\"-DSINGLE -DBANSHEE -DVEC\""], 
                      # ['16b-MP cDotp', "\"-DSINGLE -DBANSHEE -DVEC -D__CDOTP\""], 
                      # ['8b-MP', "\"-DSINGLE -DBANSHEE\""],
                      # ['8b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""],
                      ]
        vSNRdB = range(0, 40, 2)
        vITR = np.concatenate([np.full(5, 10), np.full(5, 20), np.full(5, 70), np.full(8, 90), np.full(8, 100)])
        max_it = 150
        be_target = 10
    elif run_banshee & (channel_type == "flatfading"):
        precisions = [['64b', ""],
                      # ['16b-MP', "\"-DSINGLE -DBANSHEE\""],
                      ['16b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""], 
                      ['16b-MP wDotp dgLoaded', "\"-DSINGLE -DBANSHEE -DVEC\""], 
                      # ['16b-MP cDotp', "\"-DSINGLE -DBANSHEE -DVEC -D__CDOTP\""], 
                      # ['8b-MP', "\"-DSINGLE -DBANSHEE\""],
                      # ['8b-MP dgLoaded', "\"-DSINGLE -DBANSHEE\""],
                      # ['8b-MP wDotp', "\"-DSINGLE -DBANSHEE -DVEC\""],
                      ]
        vSNRdB = range(0, 40, 4)
        vITR = np.concatenate([np.full(6, 1), np.full(6, 20), np.full(4, 30), np.full(8, 40), np.full(8, 50)])
        max_it = 50
        be_target = 10
    else:
        precisions = [['64b', '']]
        vSNRdB = range(-6, 16, 2)
        vITR = np.concatenate([np.full(3, 20), np.full(5, 20), np.full(2, 50)])
        max_it = 200
        be_target = 10




    # Golden Model Data Types
    # tf.complex64: float32_real + float32_imag
    bits_dtype = np.int16
    gm_dtype_bits = 64
    if gm_dtype_bits ==32: 
        gm_dtype_cplx = np.complex64
        gm_dtype_real = np.float32
    elif gm_dtype_bits==64:
        gm_dtype_cplx = np.complex128
        gm_dtype_real = np.float64
    else:
        raise UnexpectedError('Unexpected dtype!')



    name_tag = f'{channel_type}_Tx{N_tx}_Rx{N_rx}_{constellation}_EbNo_{vSNRdB.start}_{vSNRdB.stop}_{vSNRdB.step}_perc_{len(precisions)}.npy'

    vTBE_file = os.path.join(script_dir.parents[0],f'vTBE_{name_tag}')
    vTB_file = os.path.join(script_dir.parents[0],f'vTB_{name_tag}')

    # Initialize vTBE and vTB if files exist, else start from scratch
    if os.path.exists(vTBE_file) and os.path.exists(vTB_file):
        vTBE = np.load(vTBE_file)
        vTB = np.load(vTB_file)
        print('Previous simulation loaded.')
    else:
        vTBE = np.zeros([len(precisions), len(vSNRdB)], np.float64)
        vTB = np.zeros([len(precisions), len(vSNRdB)], np.float64)
        print('Previous simulation not found. Starting from scratch!')

    # Vectors for computation
    vBER = np.zeros([len(precisions), len(vSNRdB)], np.float64)
    vMSE = np.zeros([len(precisions), len(vSNRdB)], np.float64)
    vEVM = np.zeros([len(precisions), len(vSNRdB)], np.float64)
    vVM = np.zeros(len(vSNRdB), np.float64)


 



    # Monte Carlo Params

    # coderate = 553/1024 # i=14
    coderate = 1 
   # Instanciate OFDMMIMO class
    ofdm_mimo = end2end_mimo.OFDMMIMO(scenario=channel_type, perfect_csi=True, carrier_frequency=carrier_frequency,fft_size=fft_size,
    num_ofdm_symbols=num_ofdm_symbols,subcarrier_spacing=30e3,cyclic_prefix_length=20,num_ut=N_tx,num_ut_ant=1,
    num_bs_ant=N_rx, num_bits_per_symbol=num_bits_per_symbol,coderate=coderate, dtype_bits=gm_dtype_bits)

    num_data_symbols = ofdm_mimo.get_num_data_symbols()
    # -----------------------------------------------------------
    # SNR LOOP
    # -----------------------------------------------------------

    startime = time.time()
    # Loop over the SNRs
    for iSNR in range(0, len(vSNRdB)):

        SNRdB = vSNRdB[iSNR]
        # N_itr = vITR[iSNR] * N_batch
        N_itr = max_it
        total_bits = 0
        # -----------------------------------------------------------
        # BATCH LOOP
        # -----------------------------------------------------------

        # Loop over the batches that fit the cluster L1 memory
        # for iMC in range(0, N_itr, N_batch):
        for iMC in range(0, max_it):
            # Vector for one batch results
            vxhat = np.empty(
                (len(precisions), 2 * N_tx, num_data_symbols*N_batch), dtype=gm_dtype_real)
            vbhat = np.empty(
                (len(precisions), N_tx* num_data_symbols*N_batch*num_bits_per_symbol), dtype=bits_dtype)
            vxhat_gm = np.empty((2 * N_tx, num_data_symbols*N_batch), dtype=gm_dtype_real)

            # ebno_db = SNRdB - 10*np.log10(num_bits_per_symbol*coderate)
            ebno_db = SNRdB
            b, b_hat, x, xhat, y, H, s, no_eff, num_symbols, no_db = ofdm_mimo(batch_size=N_batch, ebno_db=ebno_db, min_ut_velocity=8.3, max_ut_velocity=8.3)
            tbe, num_bits, ber = ofdm_mimo.count_total_bit_error(b,b_hat)
            vTBE[0,iSNR] += tbe
            vTB[0,iSNR] += num_bits


            # ----- Dimensions -----
            # y: [batch_size* num_rx* num_ofdm_symbols* num_effective_subcarriers, num_rx_ant]
            # h: [batch_size* num_rx* num_ofdm_symbols* num_effective_subcarriers,..
            #  ..., num_rx_ant* num_streams_per_rx(num_Interfering_streams_per_rx)]
            # s [batch_size* num_rx* num_ofdm_syms* fft_size, num_rx_ant]
            # xhat [batch_size* num_data_symbols, num_tx* num_streams]

            vN16 = cast_reshape_to_2D_real(s.numpy().real, dtype=np.float16)
            vy16 = cast_reshape_to_2D_real(y.numpy(), dtype=np.float16)
            vH16 = cast_reshape_to_2D_real(H.numpy(), dtype=np.float16)
            vx16 = cast_reshape_to_2D_real(x.numpy(), dtype=np.float16)
            vx64 = cast_reshape_to_2D_real(x.numpy(), dtype=gm_dtype_real)
            vxhat16 = cast_reshape_to_2D_real(xhat.numpy(), dtype=np.float16)
            vxhat_gm = cast_reshape_to_2D_real(xhat.numpy(), dtype=gm_dtype_real)


            # ----------------------------------------------------------------
            # BANSHEE CALL
            # ----------------------------------------------------------------

            banshee_batch_size = vy16.shape[1] # to support simple_mimo too
            if run_banshee:
                for iPrec, (precision, flag) in enumerate(precisions[1:]):
                    vN16_ = vN16
                    if 'dgLoaded' in precision:
                        vN16_ = 0.001+vN16

                    if precision in ('8b-MP', '8b-MP wDotp'):
                        vH8 = ff.array(vH16, "e5m2")
                        vN8 = ff.array(vN16_, "e5m2")
                        vy8 = ff.array(vy16, "e5m2")
                        kwargs = {'name': 'data_mimo_mmse_f8',
                                  'H': vH8, 'N': vN8, 'y': vy8,
                                  'N_tx': N_tx, 'N_rx': N_rx, 'N_itr': banshee_batch_size}
                        gen_data_header_file(DATA_DIR, '__fp8', **kwargs)
                        result = banshee_call(
                            BANSHEE_DIR, SOFTWARE_DIR, flag, "mimo_mmse_f8")
                    else:
                        kwargs = {'name': 'data_mimo_mmse_f16',
                                  'H': vH16, 'N': vN16_, 'y': vy16,
                                  'N_tx': N_tx, 'N_rx': N_rx, 'N_itr': banshee_batch_size}
                        gen_data_header_file(DATA_DIR, '__fp16', **kwargs)
                        result = banshee_call(
                            BANSHEE_DIR, SOFTWARE_DIR, flag, "mimo_mmse_f16")


                    # [2*N_tx * N_batch * num_symbols]
                    result_casted = banshee_cast_output(result.stderr)

                    # [2*N_tx, N_batch * num_symbols]
                    xhat_ = result_casted.reshape(2 * N_tx, banshee_batch_size, order='F')

                    # TO Complex: [ batch_size(N_batch * num_symbols), N_tx]
                    xhat_ = cast_reshape_to_2D_complex(  xhat_.astype(gm_dtype_real),dtype=gm_dtype_cplx )

                    b_hat_, xhat_ = ofdm_mimo.demap_banshee(xhat_, no_eff, batch_size=N_batch, num_symbols=num_symbols)
                    tbe, num_bits, ber = ofdm_mimo.count_total_bit_error(b,b_hat_)

                    vTBE[iPrec+1,iSNR] += tbe
                    vTB[iPrec+1,iSNR] += num_bits

            # ----------------------------------------------------------------
            # Save Results (for one batch)
            # ----------------------------------------------------------------

            np.save(vTBE_file, vTBE)
            np.save(vTB_file, vTB)

            # ----------------------------------------------------------------
            min_TBE = np.min(vTBE[:,iSNR])
            if min_TBE>=be_target and iMC+1>=vITR[iSNR]:
                # print(f'target TBE reached: SNR:{SNRdB} iMC:{iMC} min_TBE:{min_TBE}')
                N_itr = iMC+1
                break
            if iMC >= max_it:
                break
        # -----------------------------------------------------------
        # END BATCH LOOP
        # -----------------------------------------------------------

        # Print results at checkpoint
        elapstime = time.strftime("%Hh%Mm%Ss",
                                  time.gmtime(time.time() - startime))
        checkpoint_print = elapstime + \
            " SNR={}dB BER@{}itr= ".format(SNRdB, N_itr)

        for iPrec in range(len(vTBE)):
            vBER[iPrec][iSNR] = vTBE[iPrec][iSNR] / vTB[iPrec][iSNR]
            checkpoint_print += "{:.7f}, ".format(vBER[iPrec][iSNR] )
            
            
        print(checkpoint_print)

    # -----------------------------------------------------------
    # END SNR LOOP
    # -----------------------------------------------------------






    # Store output in file
    current_local_time = time.localtime()
    timestr = time.strftime("%Y%m%d_%H%M%S", current_local_time)
    col_names = [precision[0] for precision in precisions]
    label = f'{channel_type}_Tx{N_tx}_Rx{N_rx}_{constellation}'
    row_names = [f"{value} dB" for value in vSNRdB]
    df_ber = pd.DataFrame(np.transpose(vBER), columns=col_names, index=row_names)
    df_ber.to_excel(f"BER_{label}.ods", index=True, header=True, engine='odf')




    # Plot output
    plot_result(vBER, vEVM, vSNRdB, precisions, name_tag)



if __name__ == "__main__":
    main()