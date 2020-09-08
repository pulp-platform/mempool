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

You can also choose the compiler to build the application with using the `COMPILER` option. The possible options are `gcc` and `llvm`, the later being the default.

```bash
# Compile with GCC instead of LLVM
make COMPILER=gcc bin/hello_world
```

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

## Common Problems

- If building the GCC toolchain fails because *makeinfo/texinfo* is missing, try the following command:
  ```bash
  make MAKEINFO=true tc-riscv-gcc
  ```
