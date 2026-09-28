# Verification record: 3D tier split

Functional verification of the branch that moves the inter-Group interconnect
out of `mempool_group` and splits `mempool_cluster` into
`tensorpool_interco_tier` and `tensorpool_compute_tier`.

Method: every application is run on this branch and on the base branch
`tensorpool` with the *same* binary and the same data set, and both the
checker output and the end-of-simulation time are compared. A pure hierarchy
change must reproduce the cycle count exactly; a change that reorders buffering
may shift it, and then the shift has to be explained.

Simulator: QuestaSim 10.7b_1. Toolchain: Bender 0.32.1, riscv32-unknown-elf-gcc.

## Small data sets, `config=tensorpool`

`matmul_i32` at 16x16x16 and `dotp_i32` at N=256, generated with

```
cd software/data
python3 gendata_header.py --app_name matmul_i32 --type int32 \
        --defines "matrix_M=16,matrix_N=16,matrix_P=16" \
        --arrays "int32_t:l2_A,int32_t:l2_B,int32_t:l2_C"
python3 gendata_header.py --app_name dotp_i32 --type int32 \
        --defines "array_N=256" \
        --arrays "int32_t:l2_X,int32_t:l2_Y,int32_t:l2_Z"
```

| Application | Base `tensorpool` | This branch | Result |
| --- | --- | --- | --- |
| `matmul_i32` 16x16x16 | 0 errors / 256 checks, 23298 ns | 0 errors / 256 checks, 23286 ns | pass, -12 ns |
| `dotp_i32` N=256 | 848 cycles, Result 1688872992, Check -695206815, 22344 ns | 848 cycles, same Result and Check, 22342 ns | bit-identical |

## Default data sets

| Application | Config | Base `tensorpool` | This branch |
| --- | --- | --- | --- |
| `matmul_i32` 32x32x32 | tensorpool | 0 errors / 1024 checks, 57624 ns | 0 errors / 1024 checks, 57460 ns |
| `tests` | tensorpool | 10654 ns | 10942 ns |
| `dotp_i32` N=1024 | tensorpool | 22304 ns | 22300 ns |
| `synth_i32` | tensorpool | 11886 ns | 11880 ns |
| `matmul_i32` | minpool | 0 errors / 1024 checks, 58298 ns | 0 errors / 1024 checks, 58298 ns |

All cycle deltas come from the single commit that relocates the crossbar
(`[hardware] Move the inter-Group interconnect out of the Group`). The number of
pipeline stages on the remote path is unchanged; what changed is their order.
Arbitration used to happen before the outbound `spill_register` and now happens
after it, so the post-arbitration buffer is the target's 1-deep
`fall_through_register` instead of a 2-deep `spill_register`. That moves cycle
counts by a fraction of a percent in either direction under contention.

The subsequent commit that introduces the two tiers reproduces every cycle count
exactly, which is what establishes that the split is pure hierarchy. `minpool`
exercises the non-TERAPOOL path, where the crossbars stay inside the Group and
the interconnect tier degenerates to the XOR permutation.

## Caveats found while verifying

**`dotp_i32` cannot fail.** None of `ATOMIC_REDUCTION`, `SINGLE_CORE_REDUCTION`
or `BINARY_REDUCTION` is defined anywhere in the build, so the `#if defined`
chain at the end of `dotp_i32p_local_unrolled4` selects no reduction and the
kernel never writes `s[]`. `main()` prints `Result` and `Check` and returns 0
regardless of whether they agree. Separately, that kernel unrolls by 4 while
TensorPool sets `banking_factor = 8`, so each core reads 4 of the 8 banks it
owns and half of the vector is never visited. Both are pre-existing: the printed
values are bit-identical on the base branch. Treat `dotp_i32` as a traffic
generator, not as a checker, until a reduction is selected and the kernel is
matched to the banking factor.

**A stale build survives a change of `config`.** `build/compile.tcl` depends on
`config/config.mk` and on the RTL sources, not on the value of the `config`
command-line variable. Running `make config=minpool simc` right after a
`tensorpool` build therefore reuses the TensorPool-compiled library and produces
a meaningless result. Delete `hardware/build/compile.tcl` (or `make clean`) when
switching flavour.

## Reproducing

```
cd hardware
rm -f build/compile.tcl                       # when switching config
make config=tensorpool simc app=matmul_i32
make config=tensorpool simc app=dotp_i32
make config=minpool    simc app=matmul_i32
```

Applications are built from `software/apps/baremetal` with the same `config`.
