void mempool_cholesky_q32p_fold(int32_t* pSrcA,
                                int32_t* pSrcB,
                                int32_t* pLL,
                                int32_t* pLR,
                                const uint32_t n,
                                const uint32_t n_row,
                                const uint32_t n_col,
                                const uint32_t fracBits,
                                const uint32_t nPE) ;

void mempool_cholesky_q32p_FLsqrtsum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE);

void mempool_cholesky_q32p_FRsqrtsum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE);

void mempool_cholesky_q32p_FLdivisum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE);

void mempool_cholesky_q32p_FRdivisum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE);

dump(index, 1)

void mempool_cholesky_q32p_fold(int32_t* pSrcA,
                                int32_t* pSrcB,
                                int32_t* pLL,
                                int32_t* pLR,
                                const uint32_t n,
                                const uint32_t n_row,
                                const uint32_t n_col,
                                const uint32_t fracBits,
                                const uint32_t nPE) {

    uint32_t absolute_core_id = mempool_get_core_id();
    uint32_t column_id = absolute_core_id / (n >> 2U);
    uint32_t core_id = absolute_core_id % (n >> 2U);
    uint32_t idx_row, idx_col;
    uint32_t j;

    for (j = 0; j < n; j++) {
        for (idx_col = column_id; idx_col < n_col; idx_col += n_col) {
            for(idx_row = 0; idx_row < n_row; idx_row++) {
                mempool_cholesky_q32p_FLsqrtsum(pSrcA + column_id * n, pLL + idx_col * n + idx_row * (n * N_BANKS), core_id, n, j, fracBits, nPE);
                mempool_cholesky_q32p_FRsqrtsum(pSrcB + column_id * n, pLR + idx_col * n + idx_row * (n * N_BANKS), core_id, n, j, fracBits, nPE);
            }
        }
        mempool_log_partial_barrier(2, absolute_core_id, n_col * (n >> 2U));
        for (idx_col = column_id; idx_col < n_col; idx_col += n_col) {
            for(idx_row = 0; idx_row < n_row; idx_row++) {
                mempool_cholesky_q32p_FLdivisum(pSrcA + column_id * n, pLL + idx_col * n + idx_row * (n * N_BANKS), core_id, n, j, fracBits, nPE);
                mempool_cholesky_q32p_FRdivisum(pSrcB + column_id * n, pLR + idx_col * n + idx_row * (n * N_BANKS), core_id, n, j, fracBits, nPE);
            }
        }
        mempool_log_partial_barrier(2, absolute_core_id, n_col * (n >> 2U));
    }
}




void mempool_cholesky_q32p_FLsqrtsum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE) {
    int32_t sum;
    int32_t pivot;
    uint32_t k;
    int32_t a0, a1, a2, a3;
    /* Elements on the diagonal are computed with a single core */
    if (core_id == (idx_col >> 2U)) {
        pivot = pSrc[idx_col * N_BANKS + idx_col];
        sum = 0;
        for (k = 0; k < 4 * (idx_col >> 2U); k++) {
            a0 = pL[idx_col + k * N_BANKS];
            a1 = pL[idx_col + (k + 1) * N_BANKS];
            a2 = pL[idx_col + (k + 2) * N_BANKS];
            a3 = pL[idx_col + (k + 3) * N_BANKS];
            asm volatile (
                "mul  %[a0],%[a0],%[a0];"
                "mul  %[a1],%[a1],%[a1];"
                "mul  %[a2],%[a2],%[a2];"
                "mul  %[a3],%[a3],%[a3];"
                "addi %[a0],%[a0],%[h];"
                "addi %[a1],%[a1],%[h];"
                "addi %[a2],%[a2],%[h];"
                "addi %[a3],%[a3],%[h];"
                "srai  %[a0],%[a0],%[s];"
                "srai  %[a1],%[a1],%[s];"
                "srai  %[a2],%[a2],%[s];"
                "srai  %[a3],%[a3],%[s];"
                "add  %[sum],%[a0],%[sum];"
                "add  %[sum],%[a1],%[sum];"
                "add  %[sum],%[a2],%[sum];"
                "add  %[sum],%[a3],%[sum];"
                : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                  [sum] "+&r" (sum)
                : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                : );
        }
        switch(idx_col % 4) {
            case 3:
                a0 = pL[idx_col + k * N_BANKS];
                a1 = pL[idx_col + (k + 1) * N_BANKS];
                a2 = pL[idx_col + (k + 2) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "mul  %[a1],%[a2],%[a2];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "addi %[a2],%[a2],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "srai  %[a2],%[a2],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    "add  %[sum],%[a2],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                break;
            case 2:
                a0 = pL[idx_col + k * N_BANKS];
                a1 = pL[idx_col + (k + 1) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                break;
            case 1:
                a0 = pL[idx_col + k * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "addi %[a0],%[a0],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "+&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                break;
            case 0:
                break;
        }
        pL[idx_col * N_BANKS + idx_col] = mempool_sqrt_q32s((pivot - sum), fracBits);
    }
}

void mempool_cholesky_q32p_FRsqrtsum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE) {
    int32_t sum;
    int32_t pivot;
    uint32_t k;
    int32_t a0, a1, a2, a3;
    /* Elements on the diagonal are computed with a single core */
    if (core_id == nPE - 1 - (idx_col >> 2U)) {
        pivot = pSrc[idx_col * N_BANKS + idx_col];
        sum = 0;
        for (k = 0; k < 4 * (idx_col >> 2U); k++) {
            a0 = pL[n - 1 - idx_col + k * N_BANKS];
            a1 = pL[n - 1 - idx_col + (k + 1) * N_BANKS];
            a2 = pL[n - 1 - idx_col + (k + 2) * N_BANKS];
            a3 = pL[n - 1 - idx_col + (k + 3) * N_BANKS];
            asm volatile (
                "mul  %[a0],%[a0],%[a0];"
                "mul  %[a1],%[a1],%[a1];"
                "mul  %[a2],%[a2],%[a2];"
                "mul  %[a3],%[a3],%[a3];"
                "addi %[a0],%[a0],%[h];"
                "addi %[a1],%[a1],%[h];"
                "addi %[a2],%[a2],%[h];"
                "addi %[a3],%[a3],%[h];"
                "srai  %[a0],%[a0],%[s];"
                "srai  %[a1],%[a1],%[s];"
                "srai  %[a2],%[a2],%[s];"
                "srai  %[a3],%[a3],%[s];"
                "add  %[sum],%[a0],%[sum];"
                "add  %[sum],%[a1],%[sum];"
                "add  %[sum],%[a2],%[sum];"
                "add  %[sum],%[a3],%[sum];"
                : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                  [sum] "+&r" (sum)
                : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                : );
        }
        switch(idx_col % 4) {
            case 3:
                a0 = pL[n - 1 - idx_col + k * N_BANKS];
                a1 = pL[n - 1 - idx_col + (k + 1) * N_BANKS];
                a2 = pL[n - 1 - idx_col + (k + 2) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "mul  %[a1],%[a2],%[a2];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "addi %[a2],%[a2],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "srai  %[a2],%[a2],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    "add  %[sum],%[a2],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                break;
            case 2:
                a0 = pL[n - 1 - idx_col + k * N_BANKS];
                a1 = pL[n - 1 - idx_col + (k + 1) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                break;
            case 1:
                a0 = pL[n - 1 - idx_col + k * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "addi %[a0],%[a0],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "+&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                break;
            case 0:
                break;
        }
        pL[idx_col * N_BANKS + n - 1 - idx_col] = mempool_sqrt_q32s((pivot - sum), fracBits);
    }
}

void mempool_cholesky_q32p_FLdivisum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE) {
    int32_t sum;
    int32_t pivot, diag;
    uint32_t i, k;
    int32_t a0, a1, a2, a3;
    int32_t b0, b1, b2, b3;
    /* Elements on rows are computed in parallel, each core gets 4 rows */
    for (i = idx_col + 1; i < n; i++) {
        if (core_id == (i / 4)) {
            sum = 0;
            pivot = pSrc[i * N_BANKS + idx_col];
            diag = pL[idx_col + idx_col * N_BANKS];
            for (k = 0; k < 4 * (idx_col >> 2U); k += 4) {
                a0 = pL[i + k * N_BANKS];
                a1 = pL[i + (k + 1) * N_BANKS];
                a2 = pL[i + (k + 2) * N_BANKS];
                a3 = pL[i + (k + 3) * N_BANKS];
                b0 = pL[idx_col + k * N_BANKS];
                b1 = pL[idx_col + (k + 1) * N_BANKS];
                b2 = pL[idx_col + (k + 2) * N_BANKS];
                b3 = pL[idx_col + (k + 3) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[b0];"
                    "mul  %[a1],%[a1],%[b1];"
                    "mul  %[a2],%[a2],%[b2];"
                    "mul  %[a3],%[a3],%[b3];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "addi %[a2],%[a2],%[h];"
                    "addi %[a3],%[a3],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "srai  %[a2],%[a2],%[s];"
                    "srai  %[a3],%[a3],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    "add  %[sum],%[a2],%[sum];"
                    "add  %[sum],%[a3],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                      [sum] "+&r" (sum)
                    : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3),
                      [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
            }
            switch(idx_col % 4) {
                case 3:
                    a0 = pL[i + k * N_BANKS];
                    a1 = pL[i + (k + 1) * N_BANKS];
                    a2 = pL[i + (k + 2) * N_BANKS];
                    b0 = pL[idx_col + k * N_BANKS];
                    b1 = pL[idx_col + (k + 1) * N_BANKS];
                    b2 = pL[idx_col + (k + 2) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "mul  %[a1],%[a2],%[b2];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "addi %[a2],%[a2],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "srai  %[a2],%[a2],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        "add  %[sum],%[a2],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    break;
                case 2:
                    a0 = pL[i + k * N_BANKS];
                    a1 = pL[i + (k + 1) * N_BANKS];
                    b0 = pL[idx_col + k * N_BANKS];
                    b1 = pL[idx_col + (k + 1) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    break;
                case 1:
                    a0 = pL[i + k * N_BANKS];
                    b0 = pL[idx_col + k * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "addi %[a0],%[a0],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "+&r" (a0),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    break;
                case 0:
                    break;
            }
            pL[i + idx_col * N_BANKS] = FIX_DIV((pivot - sum), diag);
        }
    }
}

void mempool_cholesky_q32p_FRdivisum(int32_t* pSrc,
                                     int32_t* pL,
                                     uint32_t core_id,
                                     const uint32_t n,
                                     const uint32_t idx_col,
                                     const uint32_t fracBits,
                                     const uint32_t nPE) {
    int32_t sum;
    int32_t pivot, diag;
    uint32_t i, k;
    int32_t a0, a1, a2, a3;
    int32_t b0, b1, b2, b3;
    for (i = idx_col + 1; i < n; i++) {
        if (core_id == nPE - 1 - (i / 4)) {
            sum = 0;
            pivot = pSrc[i * N_BANKS + idx_col];
            diag = pL[n - 1 - idx_col + idx_col * N_BANKS];
            for (k = 0; k < 4 * (idx_col >> 2U); k += 4) {
                a0 = pL[n - 1 - i + k * N_BANKS];
                a1 = pL[n - 1 - i + (k + 1) * N_BANKS];
                a2 = pL[n - 1 - i + (k + 2) * N_BANKS];
                a3 = pL[n - 1 - i + (k + 3) * N_BANKS];
                b0 = pL[n - 1 - idx_col + k * N_BANKS];
                b1 = pL[n - 1 - idx_col + (k + 1) * N_BANKS];
                b2 = pL[n - 1 - idx_col + (k + 2) * N_BANKS];
                b3 = pL[n - 1 - idx_col + (k + 3) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[b0];"
                    "mul  %[a1],%[a1],%[b1];"
                    "mul  %[a2],%[a2],%[b2];"
                    "mul  %[a3],%[a3],%[b3];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "addi %[a2],%[a2],%[h];"
                    "addi %[a3],%[a3],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "srai  %[a2],%[a2],%[s];"
                    "srai  %[a3],%[a3],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    "add  %[sum],%[a2],%[sum];"
                    "add  %[sum],%[a3],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                      [sum] "+&r" (sum)
                    : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3),
                      [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
            }
            switch(idx_col % 4) {
                case 3:
                    a0 = pL[n - 1 - i + k * N_BANKS];
                    a1 = pL[n - 1 - i + (k + 1) * N_BANKS];
                    a2 = pL[n - 1 - i + (k + 2) * N_BANKS];
                    b0 = pL[n - 1 - idx_col + k * N_BANKS];
                    b1 = pL[n - 1 - idx_col + (k + 1) * N_BANKS];
                    b2 = pL[n - 1 - idx_col + (k + 2) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "mul  %[a1],%[a2],%[b2];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "addi %[a2],%[a2],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "srai  %[a2],%[a2],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        "add  %[sum],%[a2],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    break;
                case 2:
                    a0 = pL[n - 1 - i + k * N_BANKS];
                    a1 = pL[n - 1 - i + (k + 1) * N_BANKS];
                    b0 = pL[n - 1 - idx_col + k * N_BANKS];
                    b1 = pL[n - 1 - idx_col + (k + 1) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    break;
                case 1:
                    a0 = pL[n - 1 - i + k * N_BANKS];
                    b0 = pL[n - 1 - idx_col + k * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "addi %[a0],%[a0],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "+&r" (a0),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    break;
                case 0:
                    break;
            }
            pL[n - 1 - i + idx_col * N_BANKS] = FIX_DIV((pivot - sum), diag);
        }
    }
}
