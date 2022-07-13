// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id,
                 uint32_t num_cores);

void init_matrix_zeros ( int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                         uint32_t core_id, uint32_t num_cores);

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id,
                 uint32_t num_cores) {
  uint32_t const split = 8; // How many rows/columns to split the matrix into
  if (num_columns > num_rows) {
    // Parallelize over columns
    uint32_t const c_start = (num_rows / split) * (core_id % split);
    uint32_t const c_end = (num_rows / split) * ((core_id % split) + 1);
    for (uint32_t j = (core_id / split); j < num_columns;
         j += (num_cores / split)) {
      for (uint32_t i = c_start; i < c_end; ++i) {
        matrix[i * num_columns + j] = a * (int32_t)i + b * (int32_t)j + c;
      }
    }
  } else {
    // Parallelize over rows
    uint32_t const c_start = (num_columns / split) * (core_id % split);
    uint32_t const c_end = (num_columns / split) * ((core_id % split) + 1);
    for (uint32_t i = (core_id / split); i < num_rows;
         i += (num_cores / split)) {
      for (uint32_t j = c_start; j < c_end; ++j) {
        matrix[i * num_columns + j] = a * (int32_t)i + b * (int32_t)j + c;
      }
    }
  }
}

void init_matrix_zeros ( int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                         uint32_t core_id, uint32_t num_cores) {

  if(core_id == 0) {
    for(uint32_t i = 0; i < num_columns; i++) {
      for(uint32_t j = 0; j < num_rows; j++) {
          matrix[j * num_rows + i] = 0;
      }
    }
    printf("SONO QUI\n");
  }

}
