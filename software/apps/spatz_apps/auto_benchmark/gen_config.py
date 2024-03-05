import json
import sys

def dotp_config(M=32768, prec=32, core=64):
    # Create a dictionary with the configuration
    filename = "dotp.json"
    kernel   = "DOTP"
    expand   = 0

    config = {
        "kernel": kernel,
        "M": M,
        "prec": prec,
        "core": core,
        "expand": expand
    }

    # Convert the dictionary to a JSON string with desired formatting
    config_str = json.dumps(config, indent=4)

    # Replace double quotes with nothing as per the example format provided
    formatted_config_str = config_str.replace('"', '')

    # Write the configuration to the file
    with open(filename, "w") as file:
        file.write(formatted_config_str)

def fft_config(M=1024, prec=32, core=16, dual=0):
    # Create a dictionary with the configuration
    filename = "fft.json"

    config = {
        "npoints": M,
        "ncores": core,
        "prec": prec,
        "dual": dual
    }

    # Convert the dictionary to a JSON string with desired formatting
    config_str = json.dumps(config, indent=4)

    # Replace double quotes with nothing as per the example format provided
    formatted_config_str = config_str.replace('"', '')

    # Write the configuration to the file
    with open(filename, "w") as file:
        file.write(formatted_config_str)

def fft_multi_config(M=1024, prec=32, core=16, dual=0, tot_core=64):
    # Create a dictionary with the configuration
    filename = "fft.json"

    config = {
        "npoints": M,
        "ncores": core,
        "prec": prec,
        "dual": dual,
        "tot_cores": tot_core
    }

    # Convert the dictionary to a JSON string with desired formatting
    config_str = json.dumps(config, indent=4)

    # Replace double quotes with nothing as per the example format provided
    formatted_config_str = config_str.replace('"', '')

    # Write the configuration to the file
    with open(filename, "w") as file:
        file.write(formatted_config_str)

def fmatmul_config(M=256, N=256, P=256, prec=32):
    # Create a dictionary with the configuration
    filename = "matmul.json"
    kernel   = 1
    expand   = 0
    a = 0
    transpose = "false"

    config = {
        "kernel": kernel,
        "M": M,
        "N": N,
        "P": P,
        "alpha": a,
        "transpose_A": transpose,
        "transpose_B": transpose,
        "prec": 32,
        "expand": expand
    }

    # Convert the dictionary to a JSON string with desired formatting
    config_str = json.dumps(config, indent=4)

    # Replace double quotes with nothing as per the example format provided
    formatted_config_str = config_str.replace('"', '')

    # Write the configuration to the file
    with open(filename, "w") as file:
        file.write(formatted_config_str)

def bw_config(M=2048, prec=32, core=64, step=16, rnd=128, dual=0):
    # Create a dictionary with the configuration
    filename = "bw.json"
    kernel   = "BW"
    expand   = 0

    config = {
        "kernel": kernel,
        "M": M,
        "round": rnd,
        "prec": prec,
        "core": core,
        "step": step,
        "expand": expand,
        "dual": dual
    }

    # Convert the dictionary to a JSON string with desired formatting
    config_str = json.dumps(config, indent=4)

    # Replace double quotes with nothing as per the example format provided
    formatted_config_str = config_str.replace('"', '')
    print('printing...')

    # Write the configuration to the file
    with open(filename, "w") as file:
        file.write(formatted_config_str)

def main(kernel="dotp", prec=32, size=256, core=64, step=16, rnd=128, dual=0, tot_core=0):
    if (kernel == "dotp"):
        dotp_config(size, prec, core)
    elif (kernel == "fft"):
        fft_config(size, prec, core, dual)
    elif (kernel == "fft-multi"):
        fft_multi_config(size, prec, core, dual, tot_core)
    elif (kernel == "fmatmul"):
        fmatmul_config(size, size, size, prec)
    elif (kernel == "bandwidth"):
        bw_config(size, prec, core, step, rnd, dual)
    else:
        print("Unsupported kernel")

if __name__ == "__main__":
    # Check if at least one argument is provided
    if len(sys.argv) > 1:
        kernel_arg = sys.argv[1]
    else:
        kernel_arg = "dotp"  # Default value if no argument is provided

    print(len(sys.argv))

    prec_arg = sys.argv[2]
    size_arg = sys.argv[3]
    core_arg = sys.argv[4]

    if len(sys.argv) > 5:
        step_arg = sys.argv[5]
        if len(sys.argv) > 6:
            iter_arg = sys.argv[6]
        else:
            iter_arg = 8
    else:
        step_arg = 16
        iter_arg = 8

    if len(sys.argv) > 7:
        dual_arg = sys.argv[7]
    else:
        dual_arg = 0

    if kernel_arg == "fft-multi":
        tot_core = sys.argv[8]
    else:
        tot_core = 0


    # Call main with the kernel argument
    main(kernel=kernel_arg, prec=prec_arg, size=size_arg, core=core_arg, step=step_arg, rnd=iter_arg, dual=dual_arg, tot_core=tot_core)

