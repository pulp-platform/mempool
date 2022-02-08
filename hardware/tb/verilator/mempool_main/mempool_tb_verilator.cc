// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <fstream>
#include <iostream>

#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

#ifndef L2_BASE
#define L2_BASE 0x80000000
#endif
#ifndef L2_SIZE
#define L2_SIZE 0x00080000
#endif

// Histogram printing function
extern "C" void print_histogram();

int main(int argc, char **argv) {
  mempool_tb_verilator top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

#ifndef TRAFFIC_GEN
  MemArea l2_mem("TOP.mempool_tb_verilator.dut.l2_mem", L2_SIZE / 16, 16);
  memutil.RegisterMemoryArea("ram", L2_BASE, &l2_mem);
  simctrl.RegisterExtension(&memutil);
#endif

  simctrl.SetInitialResetDelay(5);
  simctrl.SetResetDuration(5);

  bool exit_app = false;
  int ret_code = simctrl.ParseCommandArgs(argc, argv, exit_app);
  if (exit_app) {
    return ret_code;
  }

  std::cout << "Simulation of MemPool" << std::endl
            << "=====================" << std::endl
            << std::endl;

  simctrl.RunSimulation();

#ifdef TRAFFIC_GEN
  // Print the latency histogram
  print_histogram();
#endif

  if (!simctrl.WasSimulationSuccessful()) {
    return 1;
  }

  return 0;
}
