// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "Halide.h"
#include <numeric>
#include <stdio.h>

using namespace std;
using namespace Halide;

int main(int argc, char **argv) {
  // Global consts
  uint32_t const KERNEL[3] = {1, 2, 1};
  uint32_t KERNEL_SUM =
      accumulate(begin(KERNEL), end(KERNEL), 0, plus<uint32_t>());
  uint32_t KERNEL_WEIGHT = KERNEL_SUM * KERNEL_SUM;

  // Input arguments
  ImageParam in(type_of<uint32_t>(), 2);
  Param<int32_t> width;
  Param<int32_t> height;
  std::vector<Argument> args(3);
  args[0] = in;
  args[1] = width;
  args[2] = height;

  // Pipeline definitions
  Var x("x"), y("y");

  Buffer<uint32_t> kernel(3);
  kernel(0) = KERNEL[0];
  kernel(1) = KERNEL[1];
  kernel(2) = KERNEL[2];
  RDom r(kernel);

  Halide::Expr kernel_weight = sum(kernel(r)) * sum(kernel(r));

  Halide::Func convolution_x("convolution_x");
  Halide::Func convolution_y("convolution_y");
  Halide::Func convolution("convolution");

  // Clamp the input
  Func input("input");
  input(x, y) = in(x, y);

  // Calculate convolution
  convolution_x(x, y) += input(x + r, y) * kernel(r);
  convolution_y(x, y) += convolution_x(x, y + r) * kernel(r);
  convolution(x, y) = convolution_y(x, y) / kernel_weight;

  in.dim(0).set_bounds(0, width);
  in.dim(1).set_bounds(0, height);
  convolution.output_buffer().dim(0).set_bounds(0, width - 2);
  convolution.output_buffer().dim(1).set_bounds(0, height - 2);

  convolution_x.update().unroll(r);
  convolution_y.update().unroll(r);
  convolution.parallel(y);

  // Quickly test the pipeline
  const uint32_t WIDTH = 16;
  const uint32_t HEIGHT = 16;
  Buffer<uint32_t> test_input(32, 32);
  for (int y = 0; y < 32; y++) {
    for (int x = 0; x < 32; x++) {
      test_input(x, y) = x + y & 0xff;
    }
  }

  Halide::ParamMap params;
  params.set(in, test_input);
  params.set(width, (int32_t)32);
  params.set(height, (int32_t)32);
  Halide::Buffer<uint32_t> output = convolution.realize(
      {30, 30}, Halide::get_jit_target_from_environment(), params);

  for (int j = 0; j < test_input.height(); j++) {
    for (int i = 0; i < test_input.width(); i++) {
      printf("%3d, ", test_input(i, j));
    }
    printf("\n");
  }
  printf("\n\n");

  for (int j = 0; j < output.height(); j++) {
    for (int i = 0; i < output.width(); i++) {
      printf("%3d, ", output(i, j));
    }
    printf("\n");
  }

  for (int y = 1; y < output.height() - 1; y++) {
    for (int x = 1; x < output.width() - 1; x++) {
      uint32_t correct = ((KERNEL[0] * KERNEL[0]) * test_input(x - 1, y - 1) +
                          (KERNEL[1] * KERNEL[0]) * test_input(x, y - 1) +
                          (KERNEL[2] * KERNEL[0]) * test_input(x + 1, y - 1) +
                          (KERNEL[0] * KERNEL[1]) * test_input(x - 1, y) +
                          (KERNEL[1] * KERNEL[1]) * test_input(x, y) +
                          (KERNEL[2] * KERNEL[1]) * test_input(x + 1, y) +
                          (KERNEL[0] * KERNEL[2]) * test_input(x - 1, y + 1) +
                          (KERNEL[1] * KERNEL[2]) * test_input(x, y + 1) +
                          (KERNEL[2] * KERNEL[2]) * test_input(x + 1, y + 1)) /
                         KERNEL_WEIGHT;
      if (output(x - 1, y - 1) != correct) {
        printf("output(%d, %d) = %d instead of %d\n", x - 1, y - 1,
               output(x - 1, y - 1), correct);
      }
    }
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
  convolution.compile_to_file("halide_pipeline.riscv", args, "halide_pipeline",
                              target);
  convolution.compile_to_llvm_assembly("halide_pipeline.riscv.ll", args,
                                       "halide_pipeline", target);
  convolution.compile_to_assembly("halide_pipeline.riscv.s", args,
                                  "halide_pipeline", target);
  convolution.compile_to_c("halide_pipeline.riscv.c", args, "halide_pipeline",
                           target);
  convolution.compile_to_lowered_stmt("halide_pipeline.riscv.html", args, HTML,
                                      target);
  printf("Cross-compilation successful!\n");

  return 0;
}
