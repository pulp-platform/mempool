// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "Halide.h"
#include <stdio.h>

using namespace Halide;

int main(int argc, char **argv) {
  ImageParam in(type_of<uint8_t>(), 2);

  std::vector<Halide::Argument> args = {in};

  Func hist("hist"), cdf("cdf"), equalized("equalized"), rescaled("rescaled");
  RDom r(in), ri(0, 255);
  Var x, y, xy, i;

  // Compute the histogram
  hist(x) = cast<int>(0);
  hist(clamp(cast<uint8_t>(in(r.x, r.y)), 0, 255)) += cast<int>(1);

  // Integrate it to produce a cdf
  cdf(i) = 0;
  cdf(ri.x) = cdf(ri.x - 1) + hist(ri.x);

  // Remap the input using the cdf
  equalized(x, y) = cdf(in(x, y));

  // Scale the result back to 8-bit
  Expr pixels = in.width() * in.height();
  rescaled(x, y) = cast<uint8_t>((equalized(x, y) * 256) / pixels);

  // Schedule
  // hist.compute_root();
  // cdf.compute_root();
  // equalized.fuse(x, y, xy).parallel(xy);

  // /scratch/sriedel/projects/mempool/hardware/results/20220819_010409_halide-histogram_equalization_ba5bb06b
  // hist.compute_root();
  // cdf.compute_root();
  // rescaled.fuse(x, y, xy).parallel(xy);

  // /scratch/sriedel/projects/mempool/hardware/results/20220819_011320_halide-histogram_equalization_ba5bb06b
  // hist.compute_root();
  // cdf.compute_root();
  // rescaled.fuse(x, y, xy);

  //

  // Schedule
  // Func intermediate = hist.compute_root().update().rfactor({{r.y, y}});
  // intermediate.compute_root().parallel(y).update().parallel(y);
  // hist.parallel(x).update().parallel(x);
  // cdf.compute_root();
  // rescaled.fuse(x, y, xy).parallel(xy);
  Func intermediate = hist.compute_root().update().rfactor({{r.y, y}});
  intermediate.compute_root().update().parallel(y);
  // hist.compute_root();
  cdf.compute_root();
  rescaled.fuse(x, y, xy).parallel(xy);

  /*
    equalized .unroll(x) .unroll(y);

    //equalized.tile(x, y, xi, yi, 24, 32)
    equalized.tile(x, y, xi, yi, 6, 8)
        .fuse(x, y, xy)
        .parallel(xy)
        .split(yi, yi, yii, 4);

    */
  /*
    equalized.compute_at(equalized, yi)
        .vectorize(x, 8)
        .unroll(y);

    equalized.update(0)
        .reorder(x, y, k)
        .vectorize(x, 8)
        .unroll(x)
        .unroll(y)
        .unroll(k, 2);
    */

  /*
    equalized
        .bound(x, 0, A.width())
        .bound(y, 0, A.width());
  */

  // Quickly test the pipeline
  const uint32_t dim_x = 16;
  const uint32_t dim_y = 16;
  Buffer<uint8_t> test_in(dim_x, dim_y);
  for (uint8_t i = 0; i < dim_x; i++) {
    for (uint8_t j = 0; j < dim_y; j++) {
      test_in(i, j) = i + 4 * j + 32;
    }
  }

  Halide::ParamMap params;
  params.set(in, test_in);
  Halide::Buffer<uint8_t> out = rescaled.realize(
      {dim_x, dim_y}, Halide::get_jit_target_from_environment(), params);

  for (int j = 0; j < out.height(); j++) {
    for (int i = 0; i < out.width(); i++) {
      printf("%3d, ", out(i, j));
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
  rescaled.compile_to_file("halide_pipeline.riscv", args, "halide_pipeline",
                           target);
  rescaled.compile_to_llvm_assembly("halide_pipeline.riscv.ll", args,
                                    "halide_pipeline", target);
  rescaled.compile_to_assembly("halide_pipeline.riscv.s", args,
                               "halide_pipeline", target);
  rescaled.compile_to_c("halide_pipeline.riscv.c", args, "halide_pipeline",
                        target);
  rescaled.compile_to_lowered_stmt("halide_pipeline.riscv.html", args, HTML,
                                   target);
  printf("Cross-compilation successful!\n");

  return 0;
}
