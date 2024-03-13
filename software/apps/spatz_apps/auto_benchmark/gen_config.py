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

def fft_config(M=1024, prec=32, core=16):
    # Create a dictionary with the configuration
    filename = "fft.json"

    config = {
        "npoints": M,
        "ncores": core,
        "prec": prec
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
    kernel   = "GEMM"
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
        "prec": prec,
        "expand": expand
    }
    
    # Convert the dictionary to a JSON string with desired formatting
    config_str = json.dumps(config, indent=4)
    
    # Replace double quotes with nothing as per the example format provided
    formatted_config_str = config_str.replace('"', '')
    
    # Write the configuration to the file
    with open(filename, "w") as file:
        file.write(formatted_config_str)

def main(kernel="dotp", prec=32, size=256, core=64):
    if (kernel == "dotp"):
        dotp_config(size, prec, core)
    elif (kernel == "fft"):
        fft_config(size, prec, core)
    elif (kernel == "fmatmul"):
        fmatmul_config(size, prec)
    else:
        print("Unsupported kernel")

if __name__ == "__main__":
    # Check if at least one argument is provided
    if len(sys.argv) > 1:
        kernel_arg = sys.argv[1]
    else:
        kernel_arg = "dotp"  # Default value if no argument is provided

    prec_arg = sys.argv[2]
    size_arg = sys.argv[3]
    core_arg = sys.argv[4]
    
    # Optionally, handle more arguments for prec, size, core, etc.
    # For simplicity, only kernel_arg is handled here

    # Call main with the kernel argument
    main(kernel=kernel_arg, prec=prec_arg, size=size_arg, core=core_arg)

