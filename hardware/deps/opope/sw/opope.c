// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//

#include <stdint.h>
#include "opope_utils.h"
#include "archi_opope.h"
#include "hal_opope.h"

#include "x_input.h"
#include "w_input.h"
#include "y_input.h"
// #include "z_output.h"
#include "golden.h"

int main() {

  uint16_t m_size = M_SIZE;
  uint16_t n_size = N_SIZE;
  uint16_t k_size = K_SIZE;

  uint8_t *x = x_inp;
  uint8_t *w = w_inp;
  uint8_t *y = y_inp;
  // uint8_t *z = z_oup; // golden_out //1c010000

  uint8_t comp_fmt =  (COMP_FMT == FP8)     ? (uint8_t)Float8
                    : (COMP_FMT == FP16)    ? (uint8_t)Float16
                    : (uint8_t)Float32;
  uint8_t mem_fmt =   (MEM_FMT == FP8)     ? (uint8_t)Float8
                    : (MEM_FMT == FP16)    ? (uint8_t)Float16
                    : (uint8_t)Float32;

  volatile int errors = 0;
  int gold_sum = 0, check_sum = 0;
  int i, j;

  int offload_id_tmp, offload_id;

  // Start O-POPE operation and sleeping until the end of computation
  printf("Executing %dx%dx%d GeMM\n", m_size,n_size,k_size);
  printf("Triggering accelerator and going to sleep...\n");

  // Enable O-POPE
  hwpe_cg_enable();

  hwpe_soft_clear();

  while ((offload_id_tmp = hwpe_acquire_job()) < 0)
    ;

  opope_cfg((unsigned int)x, (unsigned int)w, (unsigned int)y, m_size, n_size, k_size,
              (uint8_t)gemm_ops, comp_fmt, mem_fmt); // Keep the gemm_ops GEMM for both the sdotp and the fma
  hwpe_trigger_job();

  asm volatile("wfi" ::: "memory");

  // At the end of accelerator's computation, we resume and check on results
  printf("Resumed!\n");

  // Disable O-POPE
  hwpe_cg_disable();

  if (mem_fmt == Float32)
    errors = opope32_compare_int(y, golden, m_size * k_size);
  else if (mem_fmt == Float16)
    errors = opope16_compare_int(y, golden, m_size * k_size / 2);
  // else if (mem_fmt == Float8)
  //   errors = opope8_compare_int(y, golden, m_size * k_size / 4);

  *(int *)0x80000000 = errors;

  tfp_printf("Terminated test with %d errors. See you!\n", errors);

  return errors;
}
