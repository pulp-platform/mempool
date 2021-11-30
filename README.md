[![ci](https://github.com/pulp-platform/mempool/actions/workflows/ci.yml/badge.svg)](https://github.com/pulp-platform/mempool/actions/workflows/ci.yml)
[![lint](https://github.com/pulp-platform/mempool/actions/workflows/lint.yml/badge.svg)](https://github.com/pulp-platform/mempool/actions/workflows/lint.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

# MemPool

MemPool is a many-core system targeting image processing applications. It implements 256 RISC-V cores that can access a large, shared L1 memory in at most five cycles.

This repository contains the software and hardware of MemPool, as well as infrastructure for compilation and simulation.

## Structure

The repository is structured as follows:

- `config` contains the global configurations that are used by software as well as hardware.
- `hardware` is where the RTL code and simulation scripts are.
- `scripts` contains useful scripts such as linting or formatting scripts.
- `software` provides example applications and MemPool's runtime.
- `toolchain` holds third-party packages
    * `halide` is the compiler infrastructure for the _Halide_ language.
    * `llvm-project` provides the LLVM compiler infrastructure.
    * `riscv-gnu-toolchain` contains the RISC-V GCC compiler.
    * `riscv-isa-sim` is an extended version of [Spike](https://github.com/riscv/riscv-isa-sim) and is used as the golden model and to parse simulation traces.
    * `riscv-opcodes` is an extended version of [riscv-opcodes](https://github.com/riscv/riscv-opcodes) that contains our custom image processing extension.
    * `verilator` provides the open-source RTL simulator Verilator.

## Get Started

Make sure you clone this repository recursively to get all the necessary submodules:

```bash
git submodule update --init --recursive
```

If the repository path of any submodule changes, run the following command to change your submodule's pointer to the remote repository:

```bash
git submodule sync --recursive
```

MemPool requires to patch a few hardware dependencies. To update the dependencies and apply the patches, run the following command after checking out in the project's root directory:

```bash
make update-deps
```

## Build dependencies
### Compiler

MemPool requires at least the RISC-V GCC toolchain to compile applications. It also supports LLVM, which depends on GCC. To implement image processing kernels, MemPool also supports Halide, a domain-specific language built on top of C++. Its compilation process is based on LLVM.

To build these toolchains, run the following commands in the project's root directory.

```bash
# Build both compilers (GCC and LLVM)
make toolchain
# Build only GCC
make tc-riscv-gcc
# Build only LLVM
make tc-llvm
# Build Halide
make halide
```

### RTL Simulation

We use [Bender](https://github.com/pulp-platform/bender) to generate our simulation scripts. Make sure you have Bender installed, or install it in the MemPool repository with:

```bash
# Install Bender
make bender
```

The RTL simulation, or more specifically, the tracing in the simulation, relies on the SPIKE simulator. To build it, run the following command in the project's directory:

```bash
# Build Spike
make riscv-isa-sim
```

MemPool supports ModelSim and the open-source Verilator for RTL simulation. Use the following command to build and install Verilator:
```bash
# Build Verilator
make verilator
```
You will need an LLVM installation.

## Software

### Build Applications

The `software/apps` folder contains example applications that work on MemPool. MemPool also contains some Halide example applications in the `software/halide` folder. Run the following command to build an application. E.g., `hello_world`:

```bash
# Bare-metal applications
cd software/apps
make hello_world
# Halide applications
cd software/halide
make matmul
```

You can also choose the compiler to build the application with using the `COMPILER` option. The possible options are `gcc` and `llvm`, the former being the default.

```bash
# Compile with LLVM instead of GCC
make COMPILER=llvm hello_world
```

To run applications designed for the **Xpulpimg** extension, be sure to select the `gcc` compiler option.
If all the Xpulpimg instructions implemented in Snitch at compilation time are supported by the Xpulpimg subset of the GCC compiler, you can build your application with the option `XPULPIMG` set to `1`:

```bash
# Compile with GCC supporting Xpulpimg instruction set
make COMPILER=gcc XPULPIMG=1 hello_world
```

Otherwise, if new Xpulpimg instructions have been implemented in Snitch, but the Xpulpimg extension in the compiler does not support them yet, you must be sure to use Xpulpimg instructions only in an `asm volatile` construct within your C/C++ application, and set `XPULPIMG=0`. This will work as long as Xpulpimg is a subset of Xpulpv2.

If `XPULPIMG` is not forced while launching `make`, it will be defaulted to the `xpulpimg` value configured in `config/config.mk`. Note that such parameter in the configuration file also defines whether the Xpulpimg extension is enabled or not in the RTL of the Snitch core, and whether such Xpulpimg functionalities have to be tested or not by the `riscv-tests` unit tests.

### Unit tests

The system is provided with an automatic unit tests suit for verification purposes; the tests are located in `riscv-tests/isa`, and can be launched from the top-level directory with:
```bash
make test
```
The unit tests will be compiled, simulated in Spike, and run in RTL simulation of MemPool.
The compilation and simulation (for both Spike simulator and MemPool RTL) of the unit tests also depends on the `xpulpimg` parameter in `config/config.mk`: the test cases dedicated to the Xpulpimg instructions will be compiled and simulated only if `xpulpimg=1`.
To add more tests, you must add your own ones to the `riscv-isa` infrastructure; more information can be found in `software/riscv-tests/README.md`.

The unit tests are included in the software package of `software` and can be compiled for MemPool by launching in the `software` directory:
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
make compile
# Run the simulation with the *hello_world* binary loaded
app=hello_world make sim
# For Halide applications use the `halide-` prefix: E.g., to run `matmul`:
app=halide-matmul make sim
# Run the simulation with the *some_binary* binary. This allows specifying the full path to the binary
preload=/some_path/some_binary make sim
# Run the simulation without starting the gui
app=hello_world make simc
# Generate the human-readable traces after simulation is completed
make trace
# Generate a visualization of the traces
app=hello_world make tracevis
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
to disable the use of `ccache`. Keep in mind that this will make the following compilations slower since compiled object files will no longer be cached.

If the tracer is enabled, its output traces are found under `hardware/build`, for both ModelSim and Verilator simulations.

Tracing can be controlled per core with a custom `trace` CSR register. The CSR is of type WARL and can only be set to zero or one. For debugging, tracing can be enabled persistently with the `snitch_trace` environment variable.

To get a visualization of the traces, check out the `scripts/tracevis.py` script. It creates a JSON file that can be viewed with [Trace-Viewer](https://github.com/catapult-project/catapult/tree/master/tracing) or in Google Chrome by navigating to `about:tracing`.

## License
MemPool is released under permissive open source licenses. Most of MemPool's source code is released under the Apache License 2.0 (`Apache-2.0`) see [`LICENSE`](LICENSE). The code in `hardware` is released under Solderpad v0.51 (`SHL-0.51`) see [`hardware/LICENSE`](hardware/LICENSE).

Note, MemPool includes several third-party packages with their own licenses:

### Software

- `software/runtime/printf.{c,h}` is licensed under the MIT license.
- `software/riscv-tests` is an extended version of RISC-V's [riscv-tests](https://github.com/riscv/riscv-tests/) repository licensed under a BSD license. See [`software/riscv-tests/LICENSE`](software/riscv-tests/LICENSE) for details.

### Hardware

The `hardware` folder is licensed under Solderpad v0.51 see [`hardware/LICENSE`](hardware/LICENSE). We use the following exceptions:

- `hardware/tb/dpi/elfloader.cpp` is licensed under a BSD license.
- `hardware/tb/verilator/*` is licensed under Apache License 2.0 see [`LICENSE`](LICENSE)
- `hardware/tb/verilator/lowrisc_*` contain modified versions of lowRISC's helper libraries. They are licensed under Apache License 2.0.

### Scripts

- `scripts/run_clang_format.py` is licensed under the MIT license.

### Toolchains

The following compilers can be used to build applications for MemPool:

- `toolchain/halide` is licensed under the MIT license. See [Halide's license](https://github.com/halide/Halide/blob/master/LICENSE.txt) for details.
- `toolchain/llvm-project`is licensed under the Apache License v2.0 with LLVM Exceptions. See [LLVM's DeveloperPolicy](https://llvm.org/docs/DeveloperPolicy.html#new-llvm-project-license-framework) for more details.
- `toolchain/riscv-gnu-toolchain`'s licensing information is available [here](https://github.com/pulp-platform/pulp-riscv-gnu-toolchain/blob/master/LICENSE)

We use the following RISC-V tools to parse simulation traces and keep opcodes consistent throughout the project.

- `toolchain/riscv-isa-sim` is licensed under a BSD license. See [riscv-isa-sim's license](https://github.com/riscv/riscv-isa-sim/blob/master/LICENSE) for details.
- `toolchain/riscv-opcodes` contains an extended version of [riscv-opcodes](https://github.com/riscv/riscv-opcodes) licensed under the BSD license. See [`toolchain/riscv-opcodes/LICENSE`](toolchain/riscv-opcodes/LICENSE) for details.

The open-source simulator [Verilator](https://www.veripool.org/verilator) can be used for RTL simulation.

- `toolchain/verilator` is licensed under GPL. See [Verilator's license](https://github.com/verilator/verilator/blob/master/LICENSE) for more details.

## Publication

If you want to use MemPool, you can cite us:

```
@InProceedings{MemPool2021,
    author    = {Matheus Cavalcante and Samuel Riedel and Antonio Pullini and Luca Benini},
    title     = {{MemPool}: A Shared-{L1} Memory Many-Core Cluster with a Low-Latency Interconnect},
    booktitle = {2021 Design, Automation, and Test in Europe Conference and Exhibition (DATE)},
    year      = 2021,
    month     = mar,
    address   = {Grenoble, FR},
    pages     = {701-706},
    doi       = {10.23919/DATE51398.2021.9474087}
}
```

This paper is also available at arXiv, at the following link: [arXiv:2012.02973 [cs.AR]](https://arxiv.org/abs/2012.02973).
