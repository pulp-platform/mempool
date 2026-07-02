#ifndef _FLEX_LIBFP16_H_
#define _FLEX_LIBFP16_H_

typedef union {
    float f;
    struct {
        uint32_t mantissa : 23;
        uint32_t exponent : 8;
        uint32_t sign : 1;
    } parts;
} FloatBits;

typedef uint16_t fp16;

// Convert float to FP16 (half-precision)
fp16 float_to_fp16(float value) {
    FloatBits floatBits;
    floatBits.f = value;

    uint16_t sign = floatBits.parts.sign << 15;
    int32_t exponent = floatBits.parts.exponent - 127 + 15; // adjust bias from 127 to 15
    uint32_t mantissa = floatBits.parts.mantissa >> 13;     // reduce to 10 bits

    if (exponent <= 0) {
        if (exponent < -10) return sign;   // too small
        mantissa = (floatBits.parts.mantissa | 0x800000) >> (1 - exponent);
        return sign | mantissa;
    } else if (exponent >= 0x1F) {
        return sign | 0x7C00;  // overflow to infinity
    }
    return sign | (exponent << 10) | mantissa;
}

// Convert FP16 to float
float fp16_to_float(fp16 value) {
    FloatBits floatBits;
    floatBits.parts.sign = (value >> 15) & 0x1;
    int32_t exponent = (value >> 10) & 0x1F;
    floatBits.parts.exponent = (exponent == 0) ? 0 : exponent + 127 - 15;
    floatBits.parts.mantissa = (value & 0x3FF) << 13;
    return floatBits.f;
}

// Fused multiply-add for FP16
fp16 fp16_fma(fp16 a, fp16 b, fp16 c) {
    float fa = fp16_to_float(a);
    float fb = fp16_to_float(b);
    float fc = fp16_to_float(c);
    float result = (fa * fb) + fc;
    return float_to_fp16(result);
}

void matmul_fp16(fp16 * z, fp16 * y, fp16 * x, fp16 * w, uint16_t m_size, uint16_t n_size, uint16_t k_size){
    for (int i = 0; i < m_size; ++i)
    {
        for (int j = 0; j < k_size; ++j)
        {
            z[i * k_size + j] = y[i * k_size + j];
            for (int k = 0; k < n_size; ++k)
            {
                z[i * k_size + j] = fp16_fma(x[i * n_size + k], w[k * k_size + j], z[i * k_size + j]);
            }
        }
    }
}


inline void asm_fp16_div(const fp16 *a, const fp16 *b, fp16 *c) {
    // Load the half-precision values from memory into local variables
    // Operation: cv = av / bv
    fp16 av = *a;
    fp16 bv = *b;
    fp16 cv;

    // Perform the division using RISC-V half-precision instructions
    asm volatile(
        "fmv.h.x ft0, %[av]\n"   // move half value 'av' into ft0
        "fmv.h.x ft1, %[bv]\n"   // move half value 'bv' into ft1
        "fdiv.h   ft2, ft0, ft1\n"   // ft2 = ft0 / ft1 (half-precision)
        "fmv.x.h  %[cv], ft2\n"  // move the result from ft2 to our local variable 'cv'
        : [cv] "=r"(cv)
        : [av] "r"(av), [bv] "r"(bv)
        : "ft0", "ft1", "ft2"    // clobbered registers
    );

    // Store the result back to memory
    *c = cv;
}


inline void asm_fp16_exp(const fp16 *inp, fp16 *oup)
{
    // We'll store the input and output in local half variables
    fp16 x = *inp;
    fp16 r; // Will hold the final result

    // Some half-precision constants for the series coefficients.
    // These are approximate but good enough for a small demonstration.
    //   1.0   = 0x3C00 in half
    //   0.5   = 0x3800
    //   1/6 ≈ 0.1667  -> ~ 0.166015625 in half (0x3555)
    //   1/24 ≈ 0.0417 -> ~ 0.0416564941 in half (0x2AAA)
    static const fp16 c1      = 0x3C00;     // 1
    static const fp16 cHalf   = 0x3800;     // 1/2
    static const fp16 cOneSix = 0x3555;  // 1/6
    static const fp16 cOne24  = 0x2AAA;  // 1/24

    //
    // We will do all arithmetic in half-precision registers
    // using inline assembly with RISC-V Zfh instructions:
    //   fmv.h.x   (move half bits from int register to FP register)
    //   fmul.h    (half-precision multiply)
    //   fadd.h    (half-precision add)
    //   fmv.x.h   (move half bits from FP register to int register)
    //
    // Register usage (ft0–ft3 are temporary floating registers):
    //   ft0 = x
    //   ft1 = accumulated sum
    //   ft2, ft3 = scratch for multiplications and constants
    //

    asm volatile(
        // --- Load x into ft0 ---
        "fmv.h.x   ft0, %[x]       \n"

        // --- Start with ft1 = 1.0 ---
        "fmv.h.x   ft1, %[c1]      \n"

        // ft1 = ft1 + x   => 1 + x
        "fadd.h    ft1, ft1, ft0   \n"

        // --- Compute x^2/2 ---
        // ft2 = x^2
        "fmul.h    ft2, ft0, ft0   \n"
        // ft3 = 0.5
        "fmv.h.x   ft3, %[cHalf]   \n"
        // ft2 = ft2 * ft3 => x^2/2
        "fmul.h    ft2, ft2, ft3   \n"
        // ft1 = ft1 + ft2 => (1 + x) + x^2/2
        "fadd.h    ft1, ft1, ft2   \n"

        // --- Compute x^3/6 ---
        // ft2 = (x^2/2) * x = x^3/2
        "fmul.h    ft2, ft2, ft0   \n"
        // ft3 = 1/6
        "fmv.h.x   ft3, %[cOneSix] \n"
        // ft2 = ft2 * (1/6) => x^3/6
        "fmul.h    ft2, ft2, ft3   \n"
        // ft1 += x^3/6
        "fadd.h    ft1, ft1, ft2   \n"

        // --- Compute x^4/24 ---
        // ft2 = (x^3/6) * x = x^4/6
        "fmul.h    ft2, ft2, ft0   \n"
        // ft3 = 1/24
        "fmv.h.x   ft3, %[cOne24]  \n"
        // ft2 = ft2 * (1/24) => x^4/24
        "fmul.h    ft2, ft2, ft3   \n"
        // ft1 += x^4/24
        "fadd.h    ft1, ft1, ft2   \n"

        // --- Move the final sum (ft1) to r ---
        "fmv.x.h   %[r], ft1       \n"

        : [r] "=r"(r)          // Output
        : [x] "r"(x), 
          [c1] "r"(c1), 
          [cHalf] "r"(cHalf), 
          [cOneSix] "r"(cOneSix), 
          [cOne24] "r"(cOne24)
        : "ft0", "ft1", "ft2", "ft3"
    );

    // Store result back to memory
    *oup = r;
}


inline void asm_fp16_sigmoid(const fp16 *inp, fp16 *out)
{
    // We'll need a few temporaries in half precision.
    fp16 x      = *inp;   // input
    fp16 negX;            // will hold -x
    fp16 eNegX;           // will hold exp(-x)
    fp16 sum;             // will hold (1 + eNegX)

    // A half-precision constant "1.0"
    static const fp16 ONE = 0x3C00;

    //----------------------------------------------------------------
    // 1) negX = -x
    //
    //   RISC-V Zfh does not always have a “fneg.h” mnemonic, but we
    //   can use fsgnjn.h  (sign-injection) to flip the sign of x:
    //----------------------------------------------------------------
    asm volatile(
        "fmv.h.x    ft0, %[x]          \n"  // ft0 = x
        "fsgnjn.h   ft0, ft0, ft0      \n"  // ft0 = -ft0
        "fmv.x.h    %[negX], ft0       \n"  // negX = -x
        : [negX] "=r" (negX)
        : [x] "r" (x)
        : "ft0"
    );

    //----------------------------------------------------------------
    // 2) eNegX = exp(negX)
    //    (Use your existing half-precision exponent routine)
    //----------------------------------------------------------------
    asm_fp16_exp(&negX, &eNegX);

    //----------------------------------------------------------------
    // 3) sum = 1 + eNegX
    //    We'll do half-precision addition via inline assembly.
    //----------------------------------------------------------------
    asm volatile(
        "fmv.h.x    ft1, %[one]       \n"  // ft1 = 1.0
        "fmv.h.x    ft2, %[eNegX]     \n"  // ft2 = eNegX
        "fadd.h     ft1, ft1, ft2     \n"  // ft1 = 1 + eNegX
        "fmv.x.h    %[sum], ft1       \n"  // sum = (1 + eNegX)
        : [sum] "=r" (sum)
        : [one] "r" (ONE),
          [eNegX] "r" (eNegX)
        : "ft1", "ft2"
    );

    //----------------------------------------------------------------
    // 4) *out = 1 / sum = 1 / (1 + e^{-x})
    //    Use your existing half-precision division function:
    //----------------------------------------------------------------
    asm_fp16_div(&ONE, &sum, out);

    // done:  *out is the sigmoid of *inp
}

/*
 * asm_fp16_compare:
 *   Returns -1 if (*a < *b), 0 if (*a == *b), +1 if (*a > *b).
 *   Purely uses half-precision RISC-V instructions for the compare.
 */
int asm_fp16_compare(const fp16 *a, const fp16 *b)
{
    // Copy inputs into local half-precision variables.
    fp16 av = *a;
    fp16 bv = *b;

    // We'll compute diff = (av - bv) in half precision.
    // Then move the bits of diff into a 16-bit integer.
    uint16_t diff_bits;

    asm volatile(
        // Move av, bv into FP registers
        "fmv.h.x    ft0, %[av]         \n"
        "fmv.h.x    ft1, %[bv]         \n"
        // diff = av - bv
        "fsub.h     ft2, ft0, ft1      \n"
        // Move bits of diff from ft2 into diff_bits
        "fmv.x.h    %[diff_bits], ft2  \n"
        : [diff_bits] "=r"(diff_bits)
        : [av] "r"(av), [bv] "r"(bv)
        : "ft0", "ft1", "ft2"
    );

    // Now interpret diff_bits as a 16-bit float:
    // Sign bit is bit 15: if set => negative => (av < bv)
    // If entire bits == 0 => exact zero => av == bv
    // Else => av > bv

    if (diff_bits == 0) {
        return 0;    // av == bv
    } else if (diff_bits & 0x8000) {
        return -1;   // negative sign => av < bv
    } else {
        return 1;    // positive => av > bv
    }
}

#define VFR_TYPE_ENCODE(funct6, m, vs2, vs1, funct3, vd, opcode)                    \
    ((funct6 << 26) | (m << 25) | (vs2 << 20) | (vs1 << 15) | (funct3 << 12) | (vd << 7) | \
     (opcode))

inline void asm_rvv_exp(uint32_t vs1_num, uint32_t vd_num){
    asm volatile(".word %0\n"::"i"(VFR_TYPE_ENCODE(0b001100, 0b1, 0b00000, vs1_num, 0b001, vd_num, 0b1010111)));
}
#endif