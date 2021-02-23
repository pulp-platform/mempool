# MemPool

MemPool is a multi-core system for image processing applications. The cluster is programmed via Halide-generated assembly code.

This repository contains the top-level logic and is the entry point into MemPool. All dependencies and simulation setups can be built from here.

## Get Started

Make sure you clone this repository recursively to get all the necessary submodules:

```bash
git submodule update --init --recursive
```

If the repository path of any submodule changes, run the following command to change your submodule's pointer to the remote repository:

```bash
git submodule sync --recursive
```

## Toolchains

MemPool requires at least the RISC-V GCC toolchain to compile applications, but also supports LLVM, which depends on GCC. To implement image processing kernels, MemPool also supports Halide, which is a domain specific language built on top of C++. Its compilation process is based on LLVM.

To build these toolchains, run the following commands in the project's root directory.

```bash
# Build both compilers (GCC and LLVM)
make toolchain
# Build Halide
make halide
```

The RTL simulation or more specifically, the tracing in the simulation, relies on the SPIKE simulator. To build it run the following command in the project's directory:

```bash
# Build Spike
make riscv-isa-sim
```

## Software

### Build Applications

The `apps` folder contains example applications that work on MemPool. Run the following command to build an application. E.g., `hello_world`:

```bash
cd apps
make bin/hello_world
```

You can also choose the compiler to build the application with using the `COMPILER` option. The possible options are `gcc` and `llvm`, the latter being the default.

```bash
# Compile with GCC instead of LLVM
make COMPILER=gcc bin/hello_world
```

To run applications designed for the **Xpulpimg** extension, be sure to select the `gcc` compiler option.
If all the Xpulpimg instructions implemented in Snitch at compilation time are supported by the Xpulpimg subset of the GCC compiler, you can build your application with the option `XPULPIMG` set to `1`:

```bash
# Compile with GCC supporting Xpulpimg instruction set
make COMPILER=gcc XPULPIMG=1 bin/hello_world
```

Otherwise, if new Xpulpimg instructions have been implemented in Snitch, but the Xpulpimg extension in the compiler does not support them yet, you must be sure to use Xpulpimg instructions only in an `asm volatile` construct within your C/C++ application, and set `XPULPIMG=0`. This will work as long as Xpulpimg is a subset of Xpulpv2.

If `XPULPIMG` is not forced while launching `make`, it will be defaulted to the `xpulpimg` value configured in `config/config.mk`. Note that such parameter in the configuration file also defines whether the Xpulpimg extension is enabled or not in the RTL of the Snitch core, and whether such Xpulpimg functionalities have to be tested or not by the `riscv-tests` unit tests.

### Unit tests

The system is provided with an automatic unit tests suit for verification purposes; the tests are located in `riscv-tests/isa`, and can be launched from the top-level directory with:
```bash
make test
```
The unit tests will be compiled, simulated in Spike and, finally, run on an RTL simulation of MemPool.
The compilation and simulation (for both Spike simulator and MemPool RTL) of the unit tests also depends on the `xpulpimg` parameter in `config/config.mk`: the test cases dedicated to the Xpulpimg instructions will be compiled and simulated only if `xpulpimg=1`.
To add more tests, you must add your own ones to the `riscv-isa` infrastructure; more information can be found in `apps/riscv-tests/README.md`.

The unit tests are included in the software package of `apps`, and can be compiled for MemPool by launching in the `apps` directory:
```bash
make COMPILER=gcc test
```
Note that the unit tests need to be compiled with `gcc`. The same logic of normal applications concerning the `XPULPIMG` parameter applies for tests.

### Writing Applications

MemPool follows [LLVM's coding style guidelines](https://llvm.org/docs/CodingStandards.html) when it comes to C and C++ code. We use `clang-format` to format all C code. Use `make format` in the project's root directory before committing software changes to make them conform with our style guide through *clang-format*.

## RTL Simulation

To simulate the MemPool system with ModelSim, go to the `hardware` folder, which contains all the SystemVerilog files. Use the following command to run your simulation:

```bash
# Go to the hardware folder
cd hardware
# Only compile the hardware without running the simulation.
make build
# Run the simulation with the *hello_world* binary loaded
app=hello_world make sim
# Run the simulation with the *some_binary* binary. This allows specifying the full path to the binary
preload=/some_path/some_binary make sim
# Run the simulation without starting the gui
app=hello_world make simc
# Generate the human readable traces after simulation is completed
make trace
# Automatically run the benchmark (headless), extract the traces, and log the results
app=hello_world make benchmark
```

You can set up the configuration of the system in the file `config/config.mk`, controlling the total number of cores, the number of cores per tile and whether the Xpulpimg extension is enabled or not in the Snitch core; the `xpulpimg` parameter also control the default core architecture considered when compiling applications for MemPool.

To simulate the MemPool system with Verilator use the same format, but with the target
```bash
make verilate
```
If, during the Verilator model compilation, you run out of space on your disk, use
```bash
export OBJCACHE=''
```
to disable the use of `ccache`. This will make the following compilations slower, but avoid to use storage.

If the tracer is enabled, its output traces are found under `hardware/build`, for both ModelSim and Verilator simulations.

## Common Problems

- If building the GCC toolchain fails because *makeinfo/texinfo* is missing, try the following command:
  ```bash
  make MAKEINFO=true tc-riscv-gcc
  ```
