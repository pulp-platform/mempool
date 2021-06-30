// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

extern char fake_uart;

void _putchar(char character) {
  // send char to console
  fake_uart = character;
}
