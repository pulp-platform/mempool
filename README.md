[![ci](https://github.com/pulp-platform/mempool/actions/workflows/ci.yml/badge.svg)](https://github.com/pulp-platform/mempool/actions/workflows/ci.yml)
[![lint](https://github.com/pulp-platform/mempool/actions/workflows/lint.yml/badge.svg)](https://github.com/pulp-platform/mempool/actions/workflows/lint.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

# TeraNoC – A Hybrid Mesh–Crossbar NoC for Scalable Shared-L1-Memory Clusters

**TeraNoC** is a core-to-L1-memory Network-on-Chip (NoC) design aimed at area-efficiently scaling manycore clusters to thousands of cores, sharing multi-megabytes of L1 scratchpad memory.
It is an open-source, hybrid mesh–crossbar on-chip interconnect that offers both scalability and low latency, while maintaining very low routing overhead.

---

## 🔍 Why TeraNoC?

A key challenge in on-chip interconnect design is to scale up bandwidth while maintaining low latency and high area efficiency.

- **2D meshes** scale with low wiring area and congestion overhead; however, their end-to-end latency increases with the number of hops, making them unsuitable for latency-sensitive core-to-L1-memory access.
- **Crossbars**, offer low latency, but their routing complexity grows quadratically with the number of I/Os, requiring large physical routing resources and limiting area-efficient scalability.

This two-sided interconnect bottleneck hinders the scale-up of many-core, low-latency, tightly coupled shared-memory clusters — pushing designers toward using many smaller, loosely coupled clusters, which introduces both hardware and software overhead.

**TeraNoC** adopts a hybrid Mesh–Crossbar topology, combining the scalability of 2D meshes with the low latency of crossbars.

---

## ✨ Key Features

- A hybrid Mesh–Crossbar topology that combines the low latency of fully combinational logarithmic crossbars with the scalability of 2D meshes.
  It supports low-latency, word-width, fine-grained multi-channel memory access — enabling efficient scale-up of shared-memory clusters, while remaining compatible with hierarchical physical design methodologies.

- A **router remapper** that redistributes traffic load across available channels to fully exploit multi-channel bandwidth.

- A **configurable number of read/write request channels** to maximize utilization of available physical wiring resources.

- A **physical-design-aware architecture** that simplifies multi-channel NoC implementation; channels in the same direction can be bundled for routing, easing both floorplanning and timing closure.

---

## 🗂️ Repository Structure

- This repository is originally branched from the [MemPool project](https://github.com/pulp-platform/mempool), which uses a crossbar-based hierarchical interconnect to scale up shared-memory clusters.
- TeraNoC integrates 2D mesh router designs based on the [FlooNoC project](https://github.com/pulp-platform/FlooNoC).
  - **Group-to-group (intra-cluster)** routers are designed as fine-grained 32-bit mesh routers.
  - **Cluster-to-main-memory** routers use 512-bit AXI-compatible FlooNoC routers.

This repository includes both the **hardware and software** components of **TeraNoC**, along with infrastructure for **compilation and simulation**.
By default, TeraNoC is configured to support **1024 cores** sharing **4096 banks** of **1 KiB** L1 memory (totaling 4 MiB).
Hardware configurations can be modified in [`config/config.mk`](config/config.mk).

### Directory Overview

- `config/`
  Global configurations used by both software and hardware.

- `hardware/`
  Contains RTL source code and simulation scripts.

- `scripts/`
  Utility scripts for tasks such as linting and formatting.

- `software/`
  Example applications and the runtime.

- `toolchain/`
  Third-party tools and packages:
  - `halide/` – Compiler infrastructure for the *Halide* language.
  - `llvm-project/` – LLVM compiler infrastructure.
  - `riscv-gnu-toolchain/` – RISC-V GCC compiler.
  - `riscv-isa-sim/` – Extended version of [Spike](https://github.com/riscv/riscv-isa-sim), used as the golden model and for parsing simulation traces.
  - `riscv-opcodes/` – Extended version of [riscv-opcodes](https://github.com/riscv/riscv-opcodes), including custom image processing extensions.
  - `verilator/` – Open-source RTL simulator [Verilator](https://verilator.org/).

---

## 🚀 Get Started

Make sure you **clone this repository recursively** to include all necessary submodules:

```bash
git submodule update --init --recursive
```

If any submodule repository paths change, sync your local configuration using:

```bash
git submodule sync --recursive
```

TeraNoC-based cluster design requires patching a few hardware dependencies. To update and patch them, run the following from the project root:

```bash
make update-deps
```

---

## 🛠️ Build Dependencies

### 🔧 Compiler Toolchains

The TeraNoC-based manycore cluster requires at least the **RISC-V GCC toolchain** to compile applications.
It also supports **LLVM**, which is a dependency for compiling **Halide** — a domain-specific language for image processing built on top of C++.

To build these toolchains, run:

```bash
# Build both GCC and LLVM
make toolchain

# Build only GCC
make tc-riscv-gcc

# Build only LLVM
make tc-llvm

# Build Halide
make halide
```

### 💻 RTL Simulation

We use [Bender](https://github.com/pulp-platform/bender) to generate simulation scripts.
Install Bender using:

```bash
make bender
```

Simulation tracing relies on the **SPIKE** simulator. To build it:

```bash
make riscv-isa-sim
```

TeraNoC supports simulation using both **ModelSim** and the open-source **Verilator**.
To build Verilator:

```bash
make verilator
```

> ℹ️ **Note**: LLVM is required to build Verilator.


## 🧩 Software

### 🏗️ Build Applications

Example applications are located under `software/apps`. Halide-based applications can be found in `software/apps/halide`, and OpenMP-based applications in `software/omp`.

To build an application (e.g., `hello_world`), use:

```bash
# Bare-metal applications
cd software/apps/baremetal/
make hello_world

# Halide applications
cd software/apps/halide
make matmul

# OpenMP applications
cd software/apps/omp
make omp_parallel
```

You can specify the compiler using the `COMPILER` variable. Supported options are `gcc` (default) and `llvm`:

```bash
# Compile using LLVM instead of GCC
make COMPILER=llvm hello_world
```

Applications using the **Xpulpimg** extension should be compiled using the `gcc` toolchain. If all Xpulpimg instructions implemented in Snitch are supported by the compiler, use:

```bash
# Compile with GCC including Xpulpimg support
make COMPILER=gcc XPULPIMG=1 hello_world
```

If the compiler does **not** support newly implemented Xpulpimg instructions, you must restrict their use to `asm volatile` blocks and compile with:

```bash
# Restrict Xpulpimg instructions to inline assembly
make COMPILER=gcc XPULPIMG=0 hello_world
```

If `XPULPIMG` is not explicitly set, it defaults to the value configured in `config/config.mk`.
This configuration also controls whether Xpulpimg is enabled in the Snitch core RTL and whether related unit tests should be executed.

---

### ✅ Unit Tests

TeraNoC includes an automated unit testing suite for system verification, located in `software/riscv-tests/isa`.
To launch all unit tests:

```bash
make riscv-tests
```

This process compiles the test suite, runs simulations using Spike, and then performs RTL simulation.

The test flow depends on the `xpulpimg` setting in `config/config.mk`. If `xpulpimg=1`, test cases involving Xpulpimg instructions will be included.

To add custom tests, modify the `riscv-tests` infrastructure. More details can be found in `software/riscv-tests/README.md`.

You can also compile the unit tests manually with:

```bash
cd software
make COMPILER=gcc riscv-tests
```

> 🔧 **Note**: Unit tests must be compiled using `gcc`. The same `XPULPIMG` configuration logic applies as with application builds.

---

### ✍️ Writing Applications

TeraNoC follows the [LLVM C/C++ coding standards](https://llvm.org/docs/CodingStandards.html).
Code formatting is enforced via `clang-format`.

To format your code before committing changes, run:

```bash
make format
```

---

## 🔬 RTL Simulation

To simulate the TeraNoC system using **ModelSim**, navigate to the `hardware` directory:

```bash
cd hardware

# Compile only (no simulation)
make compile

# Run simulation with the 'hello_world' application
app=apps/baremetal/hello_world make sim

# Run Halide application (e.g., matmul)
app=apps/halide/matmul make sim

# Use full path to preload a binary
preload=/path/to/binary make sim

# Run simulation without GUI
app=apps/baremetal/hello_world make simc

# Generate human-readable traces
make trace

# Generate a visual trace view
app=apps/baremetal/hello_world make tracevis

# Full headless benchmarking: run, trace, and log
app=apps/baremetal/hello_world make benchmark
```

System configurations — such as total core count, tile size, and `xpulpimg` support — are set in [`config/config.mk`](config/config.mk).

To simulate using **Verilator**, use the same command format, replacing `sim` with:

```bash
make verilate
```

If you encounter disk space issues during Verilator compilation, disable `ccache`:

```bash
export OBJCACHE=''
```

> ⚠️ Disabling object caching may slow down subsequent builds.

Trace files (from both ModelSim and Verilator) are generated under `hardware/build/` when tracing is enabled.

Tracing can be controlled per-core via a `trace` CSR register (type: WARL, values: 0 or 1). For persistent debug tracing, set the environment variable:

```bash
export snitch_trace=1
```

To visualize traces, use the provided script:

```bash
scripts/tracevis.py
```

This generates a JSON file viewable in:
- [Trace Viewer](https://github.com/catapult-project/catapult/tree/master/tracing)
- Google Chrome via `about:tracing`

---

### 🧪 RTL Linting

TeraNoC includes [Spyglass](https://www.synopsys.com/verification/static-and-formal-verification/spyglass.html) linting support.
Run the following in the `hardware` directory to perform lint checks:

```bash
make lint
```

This uses the `lint_rtl` target with the current configuration in `config/config.mk`.

---

## DRAMsys Co-Simulation

The cluster supports both on-chip SRAM or off-chip DRAM co-simulation for higher hierarchy memory transfering. For off-chip DRAM co-simulation, it incorporates the `dram_rtl_sim` tool as a submodule, build at `hardware/deps/dram_rtl_sim`. Leveraging DRAMSys5.0, it facilitates an effective co-simulation environment between RTL models and DRAMSys5.0 for the simulation of DRAM + CTRL models, with contemporary off-chip DRAM technologies (e.g., LPDDR, DDR, HBM).

The DRAMsys tool aids are open-sourced and can be found here:
[https://github.com/pulp-platform/dram_rtl_sim](https://github.com/pulp-platform/dram_rtl_sim)

### Building DRAMsys Co-Simulation

To prepare for DRAMsys co-simulation, adjust the system configuration by setting `l2_sim_type` to `dram` in `config/config.mk`. Then, execute the following command in the project's root directory to establish the DRAMsys tool aids environment:

```bash
make setup-dram
```

This makefile target automates several tasks:
1. Cleans up the existing DRAMSys5.0 repository, if previously built.
2. Rebuilds the DRAMSys5.0 repository and applies necessary patches within `hardware/deps/dramsys_rtl_sim/dramsys_lib/`.
3. Applies HBM2 DRAM configuration patches tailored for the cluster simulation.
4. Compiles the DRAMSys dynamic linkable library located at `hardware/deps/dramsys_rtl_sim/dramsys_lib/DRAMSys`.

**Important:** This environment requires `cmake` version 3.28.1 or higher and GCC version 11.2.0 or above.

### DRAM Chip Configuration

DRAMsys supports a range of contemporary off-chip DRAM technologies, including LPDDR, DDR, and HBM. Configuration files, formatted as `.json`, are accessible in the following directory: `hardware/deps/dramsys_rtl_sim/dramsys_lib/DRAMSys/configs`. Additionally, we provide a recommended HBM2 configuration located within `hardware/deps/dramsys_rtl_sim/dramsys_lib/DRAMSys`. This configuration is automatically applied as the default setting when establishing the DRAMsys tool aids environment. You are encouraged to review and modify these configurations as necessary to meet your specific simulation requirements.

### Testing Cluster-DRAMSys Co-Simulation

For data transfer testing between the shared-memory cluster and higher hierarchy memory through DMA transfer, use the prepared example kernel located in `software/tests/baremetal/memcpy`. For more detailed methods on building applications and setting up RTL simulation, please refer to the sections aboves.

**Note:** Currently, the simulation crafting tool for off-chip DRAM co-simulation is not open-sourced. We utilize the `Questasim` simulator exclusively.

---

## 📚 Publications

Relevant publications and documentation will be listed here soon. Stay tuned!

---

## License

TeraNoC is released under permissive open source licenses. Most of TeraNoC's source code is released under the Apache License 2.0 (`Apache-2.0`) see [`LICENSE`](LICENSE). The code in `hardware` is released under Solderpad v0.51 (`SHL-0.51`) see [`hardware/LICENSE`](hardware/LICENSE).

Note, TeraNoC includes several third-party packages with their own licenses:

<details>
<summary><i>Note, TeraNoC includes several third-party packages with their own licenses:</i></summary>
<p>

### Software

- `software/runtime/printf.{c,h}` is licensed under the MIT license.
- `software/runtime/omp/libgomp.h` is licensed under the GPL license.
- `software/riscv-tests` is an extended version of RISC-V's [riscv-tests](https://github.com/riscv/riscv-tests/) repository licensed under a BSD license. See [`software/riscv-tests/LICENSE`](software/riscv-tests/LICENSE) for details.

### Hardware

The `hardware` folder is licensed under Solderpad v0.51 see [`hardware/LICENSE`](hardware/LICENSE). We use the following exceptions:

- `hardware/tb/dpi/elfloader.cpp` is licensed under a BSD license.
- `hardware/tb/verilator/*` is licensed under Apache License 2.0 see [`LICENSE`](LICENSE)
- `hardware/tb/verilator/lowrisc_*` contain modified versions of lowRISC's helper libraries. They are licensed under Apache License 2.0.

### Scripts

- `scripts/run_clang_format.py` is licensed under the MIT license.

### Toolchains

The following compilers can be used to build applications:

- `toolchain/halide` is licensed under the MIT license. See [Halide's license](https://github.com/halide/Halide/blob/master/LICENSE.txt) for details.
- `toolchain/llvm-project`is licensed under the Apache License v2.0 with LLVM Exceptions. See [LLVM's DeveloperPolicy](https://llvm.org/docs/DeveloperPolicy.html#new-llvm-project-license-framework) for more details.
- `toolchain/riscv-gnu-toolchain`'s licensing information is available [here](https://github.com/pulp-platform/pulp-riscv-gnu-toolchain/blob/master/LICENSE)

We use the following RISC-V tools to parse simulation traces and keep opcodes consistent throughout the project.

- `toolchain/riscv-isa-sim` is licensed under a BSD license. See [riscv-isa-sim's license](https://github.com/riscv/riscv-isa-sim/blob/master/LICENSE) for details.
- `toolchain/riscv-opcodes` contains an extended version of [riscv-opcodes](https://github.com/riscv/riscv-opcodes) licensed under the BSD license. See [`toolchain/riscv-opcodes/LICENSE`](toolchain/riscv-opcodes/LICENSE) for details.

The open-source simulator [Verilator](https://www.veripool.org/verilator) can be used for RTL simulation.

- `toolchain/verilator` is licensed under GPL. See [Verilator's license](https://github.com/verilator/verilator/blob/master/LICENSE) for more details.

### DRAMsys5.0

- The `dram_rtl_sim` submodule, located at `hardware/deps/dram_rtl_sim`, is licensed under the Solderpad Hardware License 0.51. You can review the license [here](https://github.com/pulp-platform/dram_rtl_sim/blob/main/LICENSE).
- [DRAMSys5.0](https://github.com/tukl-msd/DRAMSys) is utilized for DRAM simulations. For details on its usage and licensing, please refer to the DRAMSys5.0 [license information](https://github.com/tukl-msd/DRAMSys).

</p>
</details>
