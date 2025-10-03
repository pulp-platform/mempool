// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//

#ifndef __HAL_OPOPE_H__
#define __HAL_OPOPE_H__

#include "tensor_dim.h"

/* LOW-LEVEL HAL */
#define OPOPE_ADDR_BASE OPOPE_BASE_ADD
#define OPOPE_ADDR_SPACE 0x00000100

#define HWPE_WRITE(value, offset) *(int *)(OPOPE_ADDR_BASE + offset) = value
#define HWPE_READ(offset) *(int *)(OPOPE_ADDR_BASE + offset)

static inline void opope_x_add_set(unsigned int value) {
  HWPE_WRITE(value, OPOPE_REG_OFFS + OPOPE_REG_X_PTR);
}

static inline void opope_w_add_set(unsigned int value) {
  HWPE_WRITE(value, OPOPE_REG_OFFS + OPOPE_REG_W_PTR);
}

static inline void opope_z_add_set(unsigned int value) {
  HWPE_WRITE(value, OPOPE_REG_OFFS + OPOPE_REG_Z_PTR);
}

static inline void opope_mcfg_set(uint32_t mcfg0, uint32_t mcfg1) {
  HWPE_WRITE(mcfg0, OPOPE_REG_OFFS + OPOPE_MCFG0_PTR);
  HWPE_WRITE(mcfg1, OPOPE_REG_OFFS + OPOPE_MCFG1_PTR);
}

static inline void opope_arith_set(uint32_t arith) {
  HWPE_WRITE(arith, OPOPE_REG_OFFS + OPOPE_ARITH_PTR);
}

static inline void hwpe_trigger_job() { HWPE_WRITE(0, OPOPE_TRIGGER); }

static inline int hwpe_acquire_job() { return HWPE_READ(OPOPE_ACQUIRE); }

static inline unsigned int hwpe_get_status() { return HWPE_READ(OPOPE_STATUS); }

static inline void hwpe_soft_clear() {
  volatile int i;
  HWPE_WRITE(0, OPOPE_SOFT_CLEAR);
}

static inline void hwpe_cg_enable() { return; }

static inline void hwpe_cg_disable() { return; }

void opope_cfg(unsigned int x, unsigned int w, unsigned int z, uint16_t m_size, uint16_t n_size,
                 uint16_t k_size, uint8_t gemm_op, uint8_t comp_fmt, uint8_t mem_fmt) {

  uint32_t mcfg_reg0 = 0;
  uint32_t mcfg_reg1 = 0;
  uint32_t arith_reg = 0;

  mcfg_reg0 = (k_size << 16) | (m_size << 0);
  mcfg_reg1 = n_size << 0;

  // [MACFG][ 9: 7]):   Memory  format float32
  // [MACFG][ 19: 17]): Compute format float16 or float32

  tfp_printf("comp_fmt: %d, gemm_op: %d, mem_fmt: %d\n", comp_fmt, gemm_op, mem_fmt);
  arith_reg =  (comp_fmt <<17) | (gemm_op << 10) | (mem_fmt << 7);

  opope_x_add_set((unsigned int)x);
  opope_w_add_set((unsigned int)w);
  opope_z_add_set((unsigned int)z);
  opope_mcfg_set((unsigned int)mcfg_reg0, (unsigned int)mcfg_reg1);
  opope_arith_set((unsigned int)arith_reg);
}

#endif
