// Copyright lowRISC contributors.
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

int main(int argc, char **argv) {
  mempool_tb_verilator top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  MemAreaLoc l2_mem = {.base = L2_BASE, .size = L2_SIZE};
  memutil.RegisterMemoryArea("ram", "TOP.mempool_tb_verilator.dut.l2_mem", 128,
                             &l2_mem);
  simctrl.RegisterExtension(&memutil);

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

  if (!simctrl.WasSimulationSuccessful()) {
    return 1;
  }

  return 0;
}
