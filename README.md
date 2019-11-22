# MemPool

This repository will contain the MemPool system. Currently, it sets up the MemPool software stack and virtual platform.

Note: This repository will clone external submodules, which have their own licenses. Specifically, we rely on [Halide](https://github.com/halide/Halide), the [LLVM Compiler Infrastructure](https://github.com/llvm/llvm-project), and the [RISC-V GNU Compiler Toolchain](https://github.com/pulp-platform/pulp-riscv-gnu-toolchain).

## Structure

- `apps`: Example applications for the MemPool system
- `scripts`: Setup scripts to configure the environment and install the correct dependencies
- `toolchain`: Contains the compiler toolchain

## How To

Recursively clone this repository:

```bash
git clone --recurse-submodules https://github.com/pulp-platform/mempool.git
# Or:
git clone https://github.com/pulp-platform/mempool.git
git submodule update --init --recursive

```
Configure the script [`scripts/env.sh`](scripts/env.sh), which will set up the environment. You can modify the tool version you prefer in this script. For example with the following command to use g++ version 8.2.0. You can remove this command to use the system's default version.
```bash
set_preferred_tool CXX g++-8.2.0
```
You can also configure whether you want to use HTTPS or SSH for cloning the git repositories with the `GIT_USE_SSH` flag.

The following commands set up the environment and build the toolchain
```bash
source scripts/env.sh
make toolchain
```

After the toolchain, or more specifically the pulp-sdk, is built, the environment needs to be reconfigured before compiling applications. The easies way is to source the environment script once more:
```bash
source scripts/env.sh
```

An example application can be run by either calling
```bash
make app
```
in the root directory, or by calling
```bash
make gradient all run
```
in the application directory.

# License

All sources are released under Apache Version 2.0. See the [LICENSE](LICENSE) file for more information.
