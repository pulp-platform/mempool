# Vectorized FFT on Multi-Core

The calculation is divided into `log2(NFFT)` stages. The first `log2(CORES)` stages will be phase 1, remaining being phase 2.

Data will be interchanged across cores in phase 1, therefore barrier is necessary after each stages.

There is no data dependency across cores in phase 2. Each cores are more like doing its own single-core FFT in phase 2.

The number of cores used has to be a power of two: 2, 4, 8, ...

The size of FFT cannot exceed 65536 (2^16)
