#define ATOMIC_OP(op, asm_op, I, asm_type, c_type, prefix)                     \
  static __always_inline void atomic##prefix##_##op(c_type i,                  \
                                                    atomic##prefix##_t *v) {   \
    __asm__ __volatile__("   amo" #asm_op "." #asm_type " zero, %1, %0"        \
                         : "+A"(v->counter)                                    \
                         : "r"(I)                                              \
                         : "memory");                                          \
  }

#ifdef CONFIG_GENERIC_ATOMIC64
#define ATOMIC_OPS(op, asm_op, I) ATOMIC_OP(op, asm_op, I, w, int, )
#else
#define ATOMIC_OPS(op, asm_op, I)                                              \
  ATOMIC_OP(op, asm_op, I, w, int, )                                           \
  ATOMIC_OP(op, asm_op, I, d, long, 64)
#endif

ATOMIC_OPS(add, add, i)
ATOMIC_OPS(sub, add, -i)
ATOMIC_OPS(and, and, i)
ATOMIC_OPS(or, or, i)
ATOMIC_OPS(xor, xor, i)
