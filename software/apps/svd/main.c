#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "nrutil.h"
#include "svd.c"


// Define Matrix dimensions:
#define M 4
#define N 32

int32_t matrix_U[M * N] __attribute__((section(".l1_prio")));
int32_t matrix_V[M * N] __attribute__((section(".l1_prio")));
int32_t matrix_W[N] __attribute__((section(".l1_prio")));

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

void init_vector(int32_t *vector, uint32_t num_el,
                 int32_t a, int32_t b, uint32_t core_id) {
  uint32_t const split = 8; // How many blocks to split the vector into
  uint32_t const reminder = num_el % split;
  uint32_t i, j;
  for (i = core_id * split; i < core_id * split + split; i++) {
    j = i % split;
    vector[i] = a * (int32_t)j + b;
  }
  while (i < reminder) {
    j = i % split;
    vector[i] = a * (int32_t)j + b;
  }
}

int volatile error __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    error = 0;
  }

  int32_t const U_a = 1;
  int32_t const U_b = 1;
  int32_t const U_c = -32;
  int32_t const V_a = 2;
  int32_t const V_b = 1;
  int32_t const V_c = 16;
  // Init matrix
  init_matrix(matrix_U, M, N, U_a, U_b, U_c, core_id, num_cores);
  init_matrix(matrix_V, M, N, V_a, V_b, V_c, core_id, num_cores);
  init_vector(matrix_W, N, V_a, V_b, core_id);
  mempool_barrier(num_cores);

  if (core_id == 0) {
    // Test the Matri x SVD
    svdcmp(matrix_U, M, N, matrix_W, matrix_V);
  }

  // Wait until all cores have finished
  mempool_barrier(num_cores);

  return error;
}
