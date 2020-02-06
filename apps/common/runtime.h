#pragma once
#include "encoding.h"
#include <stdint.h>
#include <stddef.h>

extern char l1_alloc_base;
extern uint32_t atomic_barrier;
extern uint32_t wake_up_reg;

typedef uint32_t mempool_id_t;
typedef uint32_t mempool_timer_t;

/// Obtain the number of cores in the current cluster.
static inline mempool_id_t mempool_get_core_count() {
    extern uint32_t nr_cores_address_reg;
    return nr_cores_address_reg;
}

/// Obtain the ID of the current core.
static inline mempool_id_t mempool_get_core_id() {
    mempool_id_t r;
    asm volatile ("csrr %0, mhartid" : "=r"(r));
    return r;
}

/// Obtain a monotonically increasing cycle count.
static inline mempool_timer_t mempool_get_timer() {
    return read_csr(mcycle);
}

/// A cluster-local barrier.
static inline void mempool_barrier() {
    // // The following is a software-only barrier using AMOs.
    // uint32_t core_id = mempool_get_core_id();
    // uint32_t core_count = mempool_get_core_count();
    // uint32_t mask = 1 << core_id;
    // uint32_t others = ((1 << core_count) - 1) ^ mask;
    // if (core_id == 0) {
    //     while ((__atomic_load_n(&atomic_barrier, __ATOMIC_RELAXED) & others) != others);
    //     __atomic_or_fetch(&atomic_barrier, mask, __ATOMIC_RELAXED);
    //     while ((__atomic_load_n(&atomic_barrier, __ATOMIC_RELAXED) & others) != 0);
    //     __atomic_and_fetch(&atomic_barrier, ~mask, __ATOMIC_RELAXED);
    // } else {
    //     while ((__atomic_load_n(&atomic_barrier, __ATOMIC_RELAXED) & 1) != 0);
    //     __atomic_or_fetch(&atomic_barrier, mask, __ATOMIC_RELAXED);
    //     while ((__atomic_load_n(&atomic_barrier, __ATOMIC_RELAXED) & 1) != 1);
    //     __atomic_and_fetch(&atomic_barrier, ~mask, __ATOMIC_RELAXED);
    // }

    // The following uses the hardware barrier.
    extern uint32_t barrier_reg;
    uint32_t tmp;
    asm volatile (
        "lw %[tmp], 0(%[addr]) \n"
        "mv zero, %[tmp] \n"
        : [tmp]"=r"(tmp) : [addr]"r"(&barrier_reg)
    );
}
