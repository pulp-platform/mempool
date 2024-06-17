# MemPool-Spatz Setup Guide

This README provides a detailed guide on how to set and use MemPool-Spatz system.

## MemPool-Spatz Hardware Configurations

To use the MemPool-Spatz, we need to use configurations supporting Spatz. They are stored under `path_to_mempool_repo/config` directory. Please refer to the READNE file in that directory for more information.

Besides the normal configuration file, there are more tunable elaboration parameters for TCDM Vector Burst settings (configurations with `_burst`). The Grouped Response Factor (`RspGF`) controls the wide of response data field, and the Vector Burst Length (`MaxBurstLen`) controls the maximum length of a burst. These paramter can be modified in `path_to_mempool_repo/hardware/deps/snitch/src/tcdm_burst_pkg.sv` file. Notice that both parameter has to be a power of two, and `RspGF` needs to be smaller or equal to `MaxBurstLen` and the `N_FU` of Spatz for correct handling.


## MemPool-Spatz Software Kernels

Because of the port conflicts between Spatz and Snitch FPU and the overlapping on the functionality, Snitch FPU is not supported in this branch. Also, `XPULPIMG` has instrcution conflicts with Spatz. As a result, `XPULPIMG` cannot be used together with Spatz configurations. This may influence the scalar kernel supports for MemPool-Spatz.

For easier use, we also provide a one-click Makefile for execution. Please see next section on `Automatic Flow`. Please run the target `make clean generate` before running any kernel from the `Makefile` there to set the hardware correctly. This target would generate the `spatz_pkg` and the `bootrom` for the simulation. You may also need to generate the dram simulation files following the guide under the main `Makefile`.

To run the kernels normally, you can use the same style of running MemPool kernels, just loading with MemPool-Spatz specialized kernels, e.g. `spatz_apps/sp-dotp`.

The vector kernels for MemPool-Spatz are stored under `path_to_mempool_repo/software/apps/spatz_apps`. Here, we provide a brief introduction on some useful kernels:

### bandwidth

This kernel uses random-generated addresses from python to test the theortical bandwidth of MemPool-Spatz. You can specify the iteration of the test in the configuration file.


### sp-axpy

The single precision multi-vector-core axpy kernel.

The size of the kernel can be set through the `axpy.json` file in the `sp-axpy/data` directory. You can run `python3 sp-axpy/data/gen_data.py --cfg sp-axpy/data/axpy.cfg` to regenerate the data after modification.

You may change the `lmul` in `main.c` to modify the vector length of each core working on. `lmul = 1` will let all cores working on local data only, which usually provides the best performance.

You may skip the checking result part by setting `CHECK` to `0` in the `main.c`.


### sp-dotp

The single precision multi-vector-core dot product kernel.

The size of the kernel can be set through the `dotp.json` file in the `sp-dotp/data` directory. You can run `python3 sp-dotp/data/gen_data.py --cfg sp-dotp/data/dotp.cfg` to regenerate the data after modification.

You may change the `lmul` in `main.c` to modify the vector length of each core working on. Usually, `lmul = 4` works best for MemPool-Spatz, and `lmul = 8` works best for TeraPool-Spatz.

Notice in this kernel, the cycles spent on reduction is not counted in performance. An additional barrier is added before the reduction to grap the correct cycles spent on load and macc.


### sp-fft

The single precision multi-vector-core fft kernel.

The size of the kernel can be set through the `fft.json` file in the `sp-fft/data` directory. You can run `python3 sp-fft/data/gen_data.py --cfg sp-fft/data/fft.cfg` to regenerate the data after modification.

Note that for fft, there is a maximum number of cores can be used for a given size. In this algorithm, we require that the number of cores used should be less or equal to `NFFT/(4*N_FU)`. For example, if you wish to use all the cores of MemPool-Spatz4 (64 4-lane Spatz), you need at least the size of 1024 points in FFT (recommand to be at least 2048).

The performance calculation in the kernel is slightly higher, by treating each stage with 10 vector ops. Actually, the last stage only has 6 vector ops.

You may skip the checking result part by setting `CHECK` to `0` in the `main.c` since the checking is very slow for large kernel size.


### sp-fft-multi

The single precision multi-vector-core multi-fft kernel.

This is a modification version of `sp-fft` kernel. In this kernel, all cores will be used to work on different fft kernel in parallel. For example, if `ncores` is set to `16` and `npoint` being `2048` in the configuration, and `mempool_spatz4_fpu` configuration is used, the kernel will actually run four `2048` fft. Every 16 cores will work on one kernel.

Do to the extra loop counting, the performance of running one fft using this kernel might be slightly slower than the normal `sp-fft` kernel.

You may skip the checking result part by setting `CHECK` to `0` in the `main.c` since the checking is very slow for large kernel size.


### sp-fmatmul-opt

The single precision multi-vector-core matmul kernel.

This kernel is optimized for the MemPool memory layout. You may change the `kernel_size` to `4` if you are running small-size matmul ,e.g. 64x64x64 for MemPool-Spatz4.


## MemPool-Spatz Automatic Flow

For data collecting, you may wish to use an easier method to run the kernel. We provide a `Makefile` under `path_to_mempool_repo/software/apps/spatz_apps/automatic_benchmark` for this purpose. A detailed `make help` target is provided in the file to execute different kernels.
