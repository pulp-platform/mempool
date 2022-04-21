# Rust hello world

Please be aware that this app will not work with the standard C Makefile and scripts.

## Setup
Install [Rust](https://www.rust-lang.org/tools/install) (if not already installed).

Install the appropriate target by running:

```bash
rustup target add riscv32i-unknown-none-elf
```

## Build
To build the application, execute

```bash
cargo build --release
```

This will build the binary into the `target/riscv32i-unknown-none-elf/release/` directory.

### Investigate binary
With a proper riscv32 toolchain installed, you can look at the binary by running

```bash
riscv32-unknown-elf-objdump -Cd /path/to/binary
```

## Execute in banshee
From the sw/banshee directory in the [snitch repository](https://github.com/pulp-platform/snitch), run
```bash
SNITCH_LOG=info cargo run -- -num-cores 1 --num-clusters 1  configuration config/mempool.yaml --trace /path/to/binary
```

## Rust runtime
The rust runtime is located in `../../rust-rt`, and is based on the C runtime, as well as Rust's [riscv-rt](https://github.com/rust-embedded/riscv-rt).

Many of the settings for the project are configured in the `.cargo/config.toml` file of the application, such as the compiler and linker script.

## TODO
This is an incomplete list of open TODOs for the Rust implementation on MemPool.
- Target support for the `m` extension
- Target support for the custom snitch compiler
- Implementation of a print (preferrably through Rust's `print!` and `println!` macros)
- Multicore support
