# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).


## Unreleased

### Added
- Add `apb` dependency of version 0.2.4
- Add support for the `FENCE` instruction
- Add support for DRAMsys5.0 co-simulation
- Add support for atomics in L2

### Changes
- Add physical feasible TeraPool configuration with SubGroup hierarchy.
- Extended `tracevis.py` to support the new Perfetto UI and compress large traces
- Use custom compiler for VCS specified with `CC` and `CCX` environment variable
- Implement operand gating for SIMD and MAC Units in Snitch IPU's DSP Unit
- Add Channel Estimation application and kernels
- Update Bender to version 0.28.1
- Update default Questasim version to 2022.3
- Decrease stack size to 128 words
- Add CFFT radix-4 and radix-2 kernels
- Parametrize the performance counters
- Restructure the software folder by moving kernels, data, and tests to dedicated folders
- Add Channel Estimation based on multiplication by (1 / pilot)
- Gate the LSU output to ensure a stable handshake interface and save energy
- Update to the latest GitHub CI actions
- Update `axi` to 0.39.2
- Update `tech_cells_generic` to 0.2.13
- Update `common_cells` to 1.33.0
- Update `common_verification` to 0.2.3
- Update `register_interface` to 0.4.3
- Updated Halide to version 15
- Move instruction cache into its own dependency
- Use automatically generated control registers
- Update the CI Ubuntu version to 22.04
- Update Bender version to 0.28.2

### Fixed
- Fix type issue in `snitch_addr_demux`
- Properly disable the debugging CSRs in ASIC implementations
- Fix a bug in the  DMA's distributed midend
- Fix bugs in radix2, radix4by2 parallelization and loading of data for radix4 CFFT
- Fix performance bug in Snitch decoder
- Remove non-resettable and active-high-reset FFs

## 0.6.0 - 2023-01-09

### Added
- Add a DMA
- Add pv.pack.h xpulpv2 instruction
- Add a script to generate random data to preload the L2 memory
- Add stack overflow simulator warning using dedicated CSR
- Add mimo_mmse_f16 kernels
- Add cmatmul_f16 kernels
- Add cfft_radix4_f16 kernels
- Add chest_f16 kernels

### Fixed
- Measure the `wfi` stalls and stalls caused by `opc` properly
- Fix the allocator initialization
- After building GCC, copy `riscv.ld` required for cMake to install folder
- Disable GCC tree-loop-distribute-patterns optimizations causing stack overflows
- Disable problematic GCC `memset` and `memcpy` built-in functions

### Changed
- Increase the default AXI width to 512 for MemPool and TeraPool
- Register all control signals at hierarchy boundaries
- Upgrade to LLVM 14
- Support multiple outstanding wake-up calls in Snitch
- Clean out tracing script and improve the traces' size and checks
- Replace NUM_CORES and similar macros with function calls in software
- Fix CI runner to Ubuntu 20.04 and Python to version 3.8

## 0.5.0 - 2022-08-03

### Added
- Add Halide runtime and build scripts for applications
- Add Halide example applications (2D convolution & matrix multiplication)
- Add CI workflow for MemPool with 256 cores
- Add hierarchical AXI interconnect to the `mempool_group`
- Integrate a `traffic_generator` into the tile
- Add a trace visualization script `tracevis.py`
- Add `config` flag to set specific MemPool flavor, either `minpool` or `mempool`
- Add bypass channels through the groups for the northeast intergroup connection
- Add capability to quickly write a value via a CSR
- Support for simulation with VCS through the `simvcs` and `simcvcs` Makefile targets
- Add Load Reserved and Store Conditional from "A" standard extension of RISC-V to the TCDM adapter
- Add the `terapool` configuration
- Add read-only caches to the hierarchical AXI interconnect
- Add a `memcpy` benchmark
- Add a systolic configuration including runtime support and a matmul application
- Add `axpy` kernel
- Add Spyglass linting scripts
- Add an OpenMP runtime and example applications
- Add dotp kernels

### Fixed
- Avoid the elaboration of SVA assertions on the `reorder_buffer` module
- Fix the elaboration of constant signal with an initial value in the `mempool_system` module
- Specify Halide's library path while installing
- Fix the waves scripts to match the new hierarchy names
- Increase pending queue in icache
- Make serial lookup in icache stallable
- Generalize MemPool to have any number of groups, configured through the `num_groups` parameter
- Kernel `conv_2d` will not preload unused values anymore

### Changed
- Compile verilator and the verilated model with Clang, for a faster compilation time
- Update BibTeX reference to the MemPool DATE paper
- Rewrite the `traffic_generator` with DPI calls
- Replace group's butterflies with logarithmic interconnects
- Do not strip the binaries of debug symbols
- Remove tile's north/east TCDM connection shuffling from the groups
- Remove the reset synchronizer from the `mempool_cluster`
- Changed LSU from in-order memory responses to out-of-order memory responses
- Remove the `reorder_buffer` from the `tcdm_shim`
- Register wake-up signals and use `wfi` for barriers
- Bump the dependencies to the latest version (`common_cells`, `register_interface`, `axi`, `tech_cells_generic`)
- Use the latest version of Modelsim by default
- Consistently print Verilator's simulation time in decimal
- Add a timeout to CI stages that could run indefinitely on errors
- Deprecate `patch-hw` and replace it with the `update-deps` Makefile target, which updates and patches the dependencies.
- Bump bender to `v0.23.2`
- Bump verilator to `v4.218`
- Make the L2 memory mutli-banked
- Improve parsing speed of tracevis by caching the `addr2line` calls
- Replace `/toolchain/riscv-opcodes` by submodule
- Change `make update_opcodes` to fit with new submodule structure of `riscv-opcodes`
- Update CI to work with new submodule structure of `riscv-opcodes`
- Disable `rvv` extension for `riscv-isa-sim`
- Issue write responses to Snitch for the TCDM and AXI interconnect
- Bump axi to `v0.36.0`
- Run simulations at 500MHz by default

## 0.4.0 - 2021-07-01

### Added
- Capability to enable and disable the traces with a CSR
- CPU model for MemPool in GCC to enable correct instruction scheduling
- Added GitHub CI flow

### Changed
- Allow atomic extension to be enabled in GCC
- Replace atomic library with the corresponding builtins
- Compile all applications in the CI instead of only the ones executed
- Move Halide applications to their own directory
- Move linting scripts to `scripts` folder
- Move flat hardware dependencies to submodules
- Updated LLVM to version 12
- Updated Halide to version 12
- Run unit tests with Verilator
- Rename `mempool` `mempool_cluster`
- Restructure software folder

### Fixed
- Stall cycle counting in the trace no longer misses stalls
- Remove unwanted latches in instruction cache
- Boot ROM address offset depends on the data width of the ROM

## 0.3.0 - 2021-03-31

### Added
- Toolchain and hardware support for Xpulp instructions:
  - Post-incrementing and register-register loads and stores (`pv.lb[u]`, `pv.lh[u]`, `pv.lw`)
  - 32-bit multiply-accumulate instructions (`pv.mac`, `pv.msu`)
  - Arithmetic SIMD instructions (`pv.{add, sub, abs, avg, avgu, min, minu, max, maxu, srl, sra, sll, or, xor, and, dotsp, dotup, dotusp, sdotsp, sdotup, sdotusp}.{h, b}`
  - Sub-word manipulation SIMD instructions (`pv.{extract, extractu, insert, shuffle2}.{h, b}`)

### Fixed
- Disable the branch prediction if there are multiple early-hits
- Align end of `.text` section with the instruction cache
- Observe the code style guidelines in the matrix multiplication and convolution kernels

### Changed
- Clean-up the pedantic compilation warnings of the matrix multiplication and convolution kernels

## 0.2.0 - 2021-03-29

### Added
- Assertion checking that Snitch's instruction interface is stable during stalls

### Changed
- Update `axi` dependency to 0.27.1
- Change I$ policy to avoid evicting the cache-line currently in use
- Make the L0 cache's data latch-based and double its size
- Make the L1 cache's tag latch-based
- Serialize the L1 lookup

### Fixed
- Add a workaround for a Modelsim 2019 bug in the `axi_demux`
- Keep clang-format from reformatting the `apps/common/riscv_test.h` assembly header file

## 0.1.0 - 2021-03-17
- Initial release.
