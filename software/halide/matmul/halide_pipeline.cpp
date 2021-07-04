// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "Halide.h"
#include <stdio.h>

using namespace Halide;

int main(int argc, char **argv) {
  Halide::Param<uint32_t> mat_size;

  ImageParam A(type_of<int32_t>(), 2);
  ImageParam B(type_of<int32_t>(), 2);

  std::vector<Halide::Argument> args = {A, B};

  Var x("x"), xi("xi"), xo("xo"), y("y"), yo("yo"), yi("yi"), yii("yii"),
      xii("xii");
  Func matmul("matmul");

  RDom k(0, A.width());
  RVar ki;

  matmul(x, y) = sum(A(k, y) * B(x, k));

  Var xy;

  matmul.fuse(x, y, xy).parallel(xy);

  /*
    matmul .unroll(x) .unroll(y);

    //matmul.tile(x, y, xi, yi, 24, 32)
    matmul.tile(x, y, xi, yi, 6, 8)
        .fuse(x, y, xy)
        .parallel(xy)
        .split(yi, yi, yii, 4);

    */
  /*
    matmul.compute_at(matmul, yi)
        .vectorize(x, 8)
        .unroll(y);

    matmul.update(0)
        .reorder(x, y, k)
        .vectorize(x, 8)
        .unroll(x)
        .unroll(y)
        .unroll(k, 2);
    */

  /*
    matmul
        .bound(x, 0, A.width())
        .bound(y, 0, A.width());
  */

  // Quickly test the pipeline
  const uint32_t M = 16;
  const uint32_t N = 16;
  const uint32_t P = 16;
  Buffer<int32_t> matrix_a(M, N);
  Buffer<int32_t> matrix_b(N, P);
  for (int i = 0; i < M; i++) {
    for (int j = 0; j < N; j++) {
      matrix_a(i, j) = i + j & 0xff;
    }
  }
  for (int i = 0; i < N; i++) {
    for (int j = 0; j < P; j++) {
      matrix_b(i, j) = i + j & 0xff;
    }
  }

  Halide::ParamMap params;
  params.set(A, matrix_a);
  params.set(B, matrix_b);
  Halide::Buffer<int32_t> matrix_c =
      matmul.realize({M, P}, Halide::get_jit_target_from_environment(), params);

  for (int j = 0; j < matrix_c.height(); j++) {
    for (int i = 0; i < matrix_c.width(); i++) {
      printf("%3d, ", matrix_c(i, j));
    }
    printf("\n");
  }

  // Cross compile for RISC-V
  Halide::Target target;
  target.os = Halide::Target::NoOS;
  target.arch = Halide::Target::RISCV;
  target.bits = 32;
  std::vector<Halide::Target::Feature> riscv_features;

  // En/Disable some features
  // riscv_features.push_back(Halide::Target::Feature::Debug);
  riscv_features.push_back(Halide::Target::Feature::NoAsserts);
  riscv_features.push_back(Halide::Target::Feature::NoBoundsQuery);
  riscv_features.push_back(Halide::Target::Feature::NoRuntime);
  riscv_features.push_back(Halide::Target::Feature::RISCV_A);
  riscv_features.push_back(Halide::Target::Feature::RISCV_M);
  riscv_features.push_back(Halide::Target::Feature::SoftFloatABI);
  target.set_features(riscv_features);

  // Compile
  matmul.compile_to_file("halide_pipeline.riscv", args, "halide_pipeline",
                         target);
  matmul.compile_to_llvm_assembly("halide_pipeline.riscv.ll", args,
                                  "halide_pipeline", target);
  matmul.compile_to_assembly("halide_pipeline.riscv.s", args, "halide_pipeline",
                             target);
  matmul.compile_to_c("halide_pipeline.riscv.c", args, "halide_pipeline",
                      target);
  matmul.compile_to_lowered_stmt("halide_pipeline.riscv.html", args, HTML,
                                 target);
  printf("Cross-compilation successful!\n");

  return 0;
}
