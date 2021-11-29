# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).


## Unreleased

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

### Fixed
- Avoid the elaboration of SVA assertions on the `reorder_buffer` module
- Fix the elaboration of constant signal with an initial value in the `mempool_system` module
- Specify Halide's library path while installing
- Fix the waves scripts to match the new hierarchy names
- Increase pending queue in icache
- Make serial lookup in icache stallable

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
