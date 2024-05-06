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

The `software/apps` folder contains example applications that work on MemPool. MemPool also contains some Halide example applications in the `software/halide` folder and OpenMP applications in the `software/omp` folder. Run the following command to build an application. E.g., `hello_world`:

```bash
# Bare-metal applications
cd software/apps
make hello_world
# Halide applications
cd software/halide
make matmul
# OpenMP applications
cd software/omp
make omp_parallel
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
make riscv-tests
```
The unit tests will be compiled, simulated in Spike, and run in RTL simulation of MemPool.
The compilation and simulation (for both Spike simulator and MemPool RTL) of the unit tests also depends on the `xpulpimg` parameter in `config/config.mk`: the test cases dedicated to the Xpulpimg instructions will be compiled and simulated only if `xpulpimg=1`.
To add more tests, you must add your own ones to the `riscv-isa` infrastructure; more information can be found in `software/riscv-tests/README.md`.

The unit tests are included in the software package of `software` and can be compiled for MemPool by launching in the `software` directory:
```bash
make COMPILER=gcc riscv-tests
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

We also provide Synopsys Spyglass linting scripts in the `hardware/spyglass`. Run `make lint` in the `hardware` folder, with a specific MemPool configuration, to run the tests associated with the `lint_rtl` target.

## DRAMsys Co-Simulation

The MemPool system supports both on-chip SRAM or off-chip DRAM co-simulation for higher hierarchy memory transfering. For off-chip DRAM co-simulation, it incorporates the `dram_rtl_sim` tool as a submodule, build at `hardware/deps/dram_rtl_sim`. Leveraging DRAMSys5.0, it facilitates an effective co-simulation environment between RTL models and DRAMSys5.0 for the simulation of DRAM + CTRL models, with contemporary off-chip DRAM technologies (e.g., LPDDR, DDR, HBM).

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
3. Applies HBM2 DRAM configuration patches tailored for the MemPool system simulation.
4. Compiles the DRAMSys dynamic linkable library located at `hardware/deps/dramsys_rtl_sim/dramsys_lib/DRAMSys`.

**Important:** This environment requires `cmake` version 3.28.1 or higher and GCC version 11.2.0 or above.

### DRAM Chip Configuration

DRAMsys supports a range of contemporary off-chip DRAM technologies, including LPDDR, DDR, and HBM. Configuration files, formatted as `.json`, are accessible in the following directory: `hardware/deps/dramsys_rtl_sim/dramsys_lib/DRAMSys/configs`. Additionally, we provide a recommended HBM2 configuration for the MemPool system located within `hardware/deps/dramsys_rtl_sim/dramsys_lib/DRAMSys`. This configuration is automatically applied as the default setting when establishing the DRAMsys tool aids environment. You are encouraged to review and modify these configurations as necessary to meet your specific simulation requirements.

### Testing MemPool-DRAMSys Co-Simulation

For data transfer testing between the MemPool system and higher hierarchy memory through DMA transfer, use the prepared example kernel located in `software/tests/baremetal/memcpy`. For more detailed methods on building applications and setting up RTL simulation, please refer to the sections aboves.

**Note:** Currently, the simulation crafting tool for off-chip DRAM co-simulation is not open-sourced. We utilize the `Questasim` simulator exclusively.

## Publications
If you use MemPool in your work or research, you can cite us:

**MemPool: A Scalable Manycore Architecture with a Low-Latency Shared L1 Memory**

```
@article{Riedel2023MemPool,
  title = {{MemPool}: A Scalable Manycore Architecture with a Low-Latency Shared {L1} Memory},
  author = {Riedel, Samuel and Cavalcante, Matheus and Andri, Renzo and Benini, Luca},
  journal = {IEEE Transactions on Computers},
  year = {2023},
  volume = {72},
  number = {12},
  pages = {3561--3575},
  publisher = {IEEE Computer Society},
  doi = {10.1109/TC.2023.3307796}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10227739) and is also available on [arXiv:2303.17742 [cs.AR]](https://arxiv.org/abs/2303.17742) and the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000643341).


The following publications give more details about MemPool, its extensions, and use cases:

### 2021

<details>
<summary><i>MemPool: A Shared-L1 Memory Many-Core Cluster with a Low-Latency Interconnect</i></summary>
<p>

```
@inproceedings{Cavalcante2021MemPool,
  title = {{MemPool}: A Shared-{L1} Memory Many-Core Cluster with a Low-Latency Interconnect},
  author = {Cavalcante, Matheus and Riedel, Samuel and Pullini, Antonio and Benini, Luca},
  booktitle = {2021 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Grenoble, France},
  year = {2021},
  month = mar,
  pages = {701--706},
  publisher = {IEEE},
  doi = {10.23919/DATE51398.2021.9474087}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9474087) and is also available on [arXiv:2012.02973 [cs.AR]](https://arxiv.org/abs/2012.02973).

</p>
</details>


<details>
<summary><i>3D SoC integration, beyond 2.5D chiplets</i></summary>
<p>

```
@inproceedings{Beyne2021,
  title = {{3D} {SoC} integration, beyond {2.5D} chiplets},
  author = {Beyne, Eric and Milojevic, Dragomir and {Van Der Plas}, Geert and Beyer, Gerald},
  booktitle = {Technical Digest - International Electron Devices Meeting, IEDM},
  year = {2021},
  pages = {79--82},
  publisher = {IEEE},
  doi = {10.1109/IEDM19574.2021.9720614}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9720614).

</p>
</details>


### 2022

<details>
<summary><i>MemPool-3D: Boosting Performance and Efficiency of Shared-L1 Memory Many-Core Clusters with 3D Integration</i></summary>
<p>

```
@inproceedings{Cavalcante2022MemPool3D,
  title = {{MemPool-3D}: Boosting Performance and Efficiency of Shared-{L1} Memory Many-Core Clusters with {3D} Integration},
  author = {Cavalcante, Matheus and Agnesina, Anthony and Riedel, Samuel and Brunion, Moritz and Garcia-Ortiz, Alberto and Milojevic, Dragomir and Catthoor, Francky and Lim, Sung Kyu and Benini, Luca},
  booktitle = {2022 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Online},
  year = {2022},
  month = mar,
  pages = {394--399},
  publisher = {IEEE},
  doi = {10.23919/DATE54114.2022.9774726}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9774726) and is also available on [arXiv:2112.01168 [cs.AR]](https://arxiv.org/abs/2112.01168).

</p>
</details>


<details>
<summary><i>Hier-3D: A Hierarchical Physical Design Methodology for Face-to-Face-Bonded 3D ICs</i></summary>
<p>

```
@inproceedings{Agnesina2022,
  title = {{Hier-3D}: A Hierarchical Physical Design Methodology for Face-to-Face-Bonded {3D} ICs},
  author = {Agnesina, Anthony and Brunion, Moritz and Garcia-Ortiz, Alberto and Catthoor, Francky and Milojevic, Dragomir and Komalan, Manu and Cavalcante, Matheus and Riedel, Samuel and Benini, Luca and Lim, Sung Kyu},
  booktitle = {Proceedings of the ACM/IEEE International Symposium on Low Power Electronics and Design},
  address = {New York, NY, USA},
  year = {2022},
  month = aug,
  publisher = {Association for Computing Machinery},
  doi = {10.1145/3531437.3539702}
}
```
This paper was published on [ACM DL](https://dl.acm.org/doi/10.1145/3531437.3539702).


</p>
</details>


<details>
<summary><i>Spatz: A Compact Vector Processing Unit for High-Performance and Energy-Efficient Shared-L1 Clusters</i></summary>
<p>

```
@inproceedings{Cavalcante2022Spatz,
  title = {Spatz: A Compact Vector Processing Unit for High-Performance and Energy-Efficient Shared-{L1} Clusters},
  author = {Cavalcante, Matheus and W{\"{u}}thrich, Domenic and Perotti, Matteo and Riedel, Samuel and Benini, Luca},
  booktitle = {2022 IEEE/ACM International Conference On Computer Aided Design (ICCAD)},
  address = {San Diego, California, USA},
  year = {2022},
  month = oct,
  pages = {159--167},
  publisher = {Association for Computing Machinery},
  doi = {10.1145/3508352.3549367}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10069431) and is also available on [arXiv:2207.07970 [cs.AR]](https://arxiv.org/abs/2207.07970).

</p>
</details>


<details>
<summary><i>Thermal Performance Analysis of Mempool RISC-V Multicore SoC</i></summary>
<p>

```
@article{Venkateswarlu2022,
  title = {Thermal Performance Analysis of Mempool RISC-V Multicore {SoC}},
  author = {Venkateswarlu, Sankatali and Mishra, Subrat and Oprins, Herman and Vermeersch, Bjorn and Brunion, Moritz and Han, Jun Han and Stan, Mircea R. and Weckx, Pieter and Catthoor, Francky},
  journal = {IEEE Transactions on Very Large Scale Integration (VLSI) Systems},
  year = {2022},
  volume = {30},
  number = {11},
  pages = {1668--1676},
  publisher = {IEEE},
  doi = {10.1109/TVLSI.2022.3207553}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/9905665).

</p>
</details>


### 2023

<details>
<summary><i>Towards Chip-Package-System Co-optimization of Thermally-limited System-On-Chips (SOCs)</i></summary>
<p>

```
@inproceedings{Mishra2023,
  title = {Towards Chip-Package-System Co-optimization of Thermally-limited System-On-Chips (SOCs)},
  author = {Mishra, S. and Sankatali, V. and Vermeersch, B. and Brunion, M. and Lofrano, M. and Abdi, D. and Oprins, H. and Biswas, D. and Zografos, O. and Hiblot, G. and {Van Der Plas}, G. and Weckx, P. and Hellings, G. and Myers, J. and Catthoor, F. and Ryckaert, J.},
  booktitle = {IEEE International Reliability Physics Symposium Proceedings},
  address = {Monterey, CA, USA},
  year = {2023},
  month = mar,
  publisher = {IEEE},
  doi = {10.1109/IRPS48203.2023.10117979}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10117979).

</p>
</details>


<details>
<summary><i>Efficient Parallelization of 5G-PUSCH on a Scalable RISC-V Many-Core Processor</i></summary>
<p>

```
@inproceedings{Bertuletti2023PUSCH,
  title = {Efficient Parallelization of {5G-PUSCH} on a Scalable {RISC-V} Many-Core Processor},
  author = {Bertuletti, Marco and Zhang, Yichao and Vanelli-Coralli, Alessandro and Benini, Luca},
  booktitle = {2023 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Antwerp, Belgium},
  year = {2023},
  month = apr,
  pages = {396--401},
  publisher = {IEEE},
  doi = {10.23919/DATE56975.2023.10137247}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10137247) and is also available on [arXiv:2210.09196 [cs.DC]](https://arxiv.org/abs/2210.09196).

</p>
</details>


<details>
<summary><i>MemPool Meets Systolic: Flexible Systolic Computation in a Large Shared-Memory Processor Cluster</i></summary>
<p>

```
@inproceedings{Riedel2023MmS,
  title = {{MemPool} Meets Systolic: Flexible Systolic Computation in a Large Shared-Memory Processor Cluster},
  author = {Riedel, Samuel and Khov, Gua Hao and Mazzola, Sergio and Cavalcante, Matheus and Andri, Renzo and Benini, Luca},
  booktitle = {2023 Design, Automation, and Test in Europe Conference and Exhibition},
  address = {Antwerp, Belgium},
  year = {2023},
  month = apr,
  pages = {503--504},
  publisher = {IEEE},
  doi = {10.23919/DATE56975.2023.10136909}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10136909).

</p>
</details>


<details>
<summary><i>Fast Shared-Memory Barrier Synchronization for a 1024-Cores RISC-V Many-Core Cluster</i></summary>
<p>

```
@inproceedings{Bertuletti2023Barrier,
  title = {Fast Shared-Memory Barrier Synchronization for a 1024-Cores {RISC-V} Many-Core Cluster},
  author = {Bertuletti, Marco and Riedel, Samuel and Zhang, Yichao and Vanelli-Coralli, Alessandro and Benini, Luca},
  booktitle = {Embedded Computer Systems: Architectures, Modeling, and Simulation},
  editor = {Silvano, Cristina and Pilato, Christian and Reichenbach, Marc},
  address = {Samos},
  year = {2023},
  month = jul,
  pages = {241--254},
  publisher = {Springer Nature Switzerland},
  doi = {10.1007/978-3-031-46077-7_16}
}
```
This paper was published on [Springer Link](https://link.springer.com/chapter/10.1007/978-3-031-46077-7_16) and is also available on [arXiv:2307.10248 [cs.DC]](https://arxiv.org/abs/2307.10248) and the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000648454).

</p>
</details>


<details>
<summary><i>MemPool: A Scalable Manycore Architecture with a Low-Latency Shared L1 Memory</i></summary>
<p>

```
@article{Riedel2023MemPool,
  title = {{MemPool}: A Scalable Manycore Architecture with a Low-Latency Shared {L1} Memory},
  author = {Riedel, Samuel and Cavalcante, Matheus and Andri, Renzo and Benini, Luca},
  journal = {IEEE Transactions on Computers},
  year = {2023},
  volume = {72},
  number = {12},
  pages = {3561--3575},
  publisher = {IEEE Computer Society},
  doi = {10.1109/TC.2023.3307796}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10227739) and is also available on [arXiv:2303.17742 [cs.AR]](https://arxiv.org/abs/2303.17742) and the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000643341).

</p>
</details>


<details>
<summary><i>Impact of 3-D Integration on Thermal Performance of RISC-V MemPool Multicore SOC</i></summary>
<p>

```
@article{Venkateswarlu2023,
  title = {Impact of 3-D Integration on Thermal Performance of {RISC-V} {MemPool} Multicore {SOC}},
  author = {Venkateswarlu, Sankatali and Mishra, Subrat and Oprins, Herman and Vermeersch, Bjorn and Brunion, Moritz and Han, Jun Han and Stan, Mircea R. and Biswas, Dwaipayan and Weckx, Pieter and Catthoor, Francky},
  journal = {IEEE Transactions on Very Large Scale Integration (VLSI) Systems},
  year = {2023},
  volume = {31},
  number = {12},
  pages = {1896-1904},
  publisher = {IEEE},
  doi = {10.1109/TVLSI.2023.3314135}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10261872).

</p>
</details>


<details>
<summary><i>MinPool: A 16-core NUMA-L1 Memory RISC-V Processor Cluster for Always-on Image Processing in 65nm CMOS</i></summary>
<p>

```
@inproceedings{Riedel2023MinPool,
  author={Riedel, Samuel and Cavalcante, Matheus and Frouzakis, Manos and Wüthrich, Domenic and Mustafa, Enis and Billa, Arlind and Benini, Luca},
  title={{MinPool}: A 16-core {NUMA-L1} Memory {RISC-V} Processor Cluster for Always-on Image Processing in 65nm {CMOS}},
  booktitle={2023 30th IEEE International Conference on Electronics, Circuits and Systems (ICECS)},
  address = {Istanbul, Turkiye},
  year={2023},
  month=dec,
  pages={1--4},
  publisher={IEEE},
  doi={10.1109/ICECS58634.2023.10382925}
}
```
This paper was published on [IEEE Xplore](https://ieeexplore.ieee.org/document/10382925) and is also available on the [ETH Research Collection](https://doi.org/10.3929/ethz-b-000653598).

</p>
</details>

### 2024

<details>
<summary><i>LRSCwait: Enabling Scalable and Efficient Synchronization in Manycore Systems through Polling-Free and Retry-Free Operation</i></summary>
<p>

```
@article{Riedel2024LRSCwait,
      title={{LRSCwait}: Enabling Scalable and Efficient Synchronization in Manycore Systems through Polling-Free and Retry-Free Operation},
      author={Samuel Riedel and Marc Gantenbein and Alessandro Ottaviano and Torsten Hoefler and Luca Benini},
      journal={arXiv:2401.09359 [cs.AR]},
      year={2024},
      month=jan
}
```
This paper is available on [arXiv:2401.09359 [cs.AR]](https://arxiv.org/abs/2401.09359).

</p>
</details>


<details>
<summary><i>Enabling Efficient Hybrid Systolic Computation in Shared L1-Memory Manycore Clusters</i></summary>
<p>

```
@article{Mazzola2024Systolic,
      title={Enabling Efficient Hybrid Systolic Computation in Shared {L1}-Memory Manycore Clusters},
      author={Sergio Mazzola and Samuel Riedel and Luca Benini},
      journal={arXiv:2402.12986 [cs.AR]},
      year={2024},
      month=feb
}
```
This paper is available on [arXiv:2402.12986 [cs.AR]](https://arxiv.org/abs/2402.12986).

</p>
</details>

## Chips

The MemPool architecture has been taped out in the following chips:

- 2021 [**MinPool**](http://asic.ethz.ch/2021/Minpool.html): A 16-core prototype of MemPool.
- 2024 [**Heartstream**](http://asic.ethz.ch/2024/Heartstream.html): A 64-core version of MemPool with systolic and FPU support.

## License
MemPool is released under permissive open source licenses. Most of MemPool's source code is released under the Apache License 2.0 (`Apache-2.0`) see [`LICENSE`](LICENSE). The code in `hardware` is released under Solderpad v0.51 (`SHL-0.51`) see [`hardware/LICENSE`](hardware/LICENSE).

Note, MemPool includes several third-party packages with their own licenses:

<details>
<summary><i>Note, MemPool includes several third-party packages with their own licenses:</i></summary>
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

The following compilers can be used to build applications for MemPool:

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
