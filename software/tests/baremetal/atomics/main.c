// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "runtime.h"

uint32_t volatile l1 __attribute__((section(".l1")));
uint32_t volatile l2 __attribute__((section(".l2")));

int atomics(uint32_t volatile *addr) {
  uint32_t golden, ret, op;

  // Init
  *addr = 0x12345678;

  // AMO Swap
  golden = *addr;
  op = 0x23456789;
  asm volatile("amoswap.w %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 1;
  }

  // AMO Add
  golden = *addr;
  op = 0x199;
  asm volatile("amoadd.w  %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 11;
  }
  if (*addr != golden + op) {
    return 12;
  }

  // AMO Xor
  golden = *addr;
  op = 0x12345678;
  asm volatile("amoxor.w  %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 21;
  }
  if (*addr != (golden ^ op)) {
    return 22;
  }

  // AMO And
  golden = *addr;
  op = 0x0000FF33;
  asm volatile("amoand.w  %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 31;
  }
  if (*addr != (golden & op)) {
    return 32;
  }

  // AMO Or
  golden = *addr;
  op = 0x12340000;
  asm volatile("amoor.w   %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 41;
  }
  if (*addr != (golden | op)) {
    return 42;
  }

  // AMO Min
  golden = *addr;
  op = 0xF0000001;
  asm volatile("amomin.w  %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 51;
  }
  if (*addr != ((int32_t)golden < (int32_t)op ? golden : op)) {
    return 52;
  }

  // AMO Max
  golden = *addr;
  op = 0x00000001;
  asm volatile("amomax.w  %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 61;
  }
  if (*addr != ((int32_t)golden > (int32_t)op ? golden : op)) {
    return 62;
  }

  // AMO UMin
  golden = *addr;
  op = 0x00000010;
  asm volatile("amominu.w %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 71;
  }
  if (*addr != (golden < op ? golden : op)) {
    return 72;
  }

  // AMO UMax
  golden = *addr;
  op = 0x00000010;
  asm volatile("amomaxu.w %0, %1, (%2)" : "=r"(ret) : "r"(op), "r"(addr));
  if (ret != golden) {
    return 81;
  }
  if (*addr != (golden > op ? golden : op)) {
    return 82;
  }

  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();

  if (core_id != 0) {
    mempool_wfi();
  }

  int ret = 0;

  // L1 memory
  ret = atomics(&l1);
  if (ret) {
    return ret;
  }

  // L2 memory
  ret = atomics(&l2);
  if (ret) {
    return ret + 100;
  }

  return 0;
}
