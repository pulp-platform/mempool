// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module mempool_tb_verilator (
  input logic clk_i,
  input logic rst_ni
);

  /*****************
   *  Definitions  *
   *****************/

  import mempool_pkg::*;
  import axi_pkg::xbar_cfg_t;
  import axi_pkg::xbar_rule_32_t;

  `ifdef BOOT_ADDR
  localparam BootAddr = `BOOT_ADDR;
  `else
  localparam BootAddr = 0;
  `endif

  localparam ClockPeriod = 1ns;
  localparam TA          = 0.2ns;
  localparam TT          = 0.8ns;

  localparam L2AddrWidth = 18;

 /********************************
   *  Clock and Reset Generation  *
   ********************************/

  logic clk;
  logic rst_n;

  // Controlling the clock and reset
`ifdef VERILATOR
  assign clk = clk_i;
  assign rst_n = rst_ni;
`else
  // Toggling the clock
  always #(ClockPeriod/2) clk = !clk;
  initial begin
    clk   = 1'b1;
    rst_n = 1'b0;

    repeat (5)
      #(ClockPeriod);

    rst_n = 1'b1;
  end
`endif

  /*************************
   *  Signal declarations  *
   *************************/

  logic eoc_valid;

  axi_system_req_t  axi_mst_req;
  axi_system_resp_t axi_mst_resp;

  /*********
   *  DUT  *
   *********/

  mempool_system #(
    .TCDMBaseAddr(32'h0   ),
    .BootAddr    (BootAddr)
  ) dut (
    .clk_i          (clk          ),
    .rst_ni         (rst_n        ),
    .fetch_en_i     (1'b0         ),
    .eoc_valid_o    (eoc_valid    ),
    .busy_o         (/*Unused*/   ),
    .mst_req_o      (axi_mst_req  ),
    .mst_resp_i     (axi_mst_resp ),
    .slv_req_i      (/*Unused*/ '0),
    .slv_resp_o     (/*Unused*/   )
  );

  /**********
   *  UART  *
   **********/

  axi_uart #(
    .axi_req_t  (axi_system_req_t ),
    .axi_resp_t (axi_system_resp_t)
  ) i_axi_uart (
    .clk_i     (clk         ),
    .rst_ni    (rst_n       ),
    .testmode_i(1'b0        ),
    .axi_req_i (axi_mst_req ),
    .axi_resp_o(axi_mst_resp)
  );

  // TODO: Add XBAR and infinite host memory?

  /*********
   *  EOC  *
   *********/
  always_ff @(posedge clk) begin
    if (rst_ni && eoc_valid) begin
      $display("[EOC] Simulation ended at %t (retval = %0d).", $time, dut.i_ctrl_registers.eoc_o);
      $finish;
    end
  end

  /*********************************
   *  Ideal Instruction Interface  *
   *********************************/
  if (IdealInstructionInterface) begin
    for (genvar g = 0; unsigned'(g) < NumGroups; g++) begin: gen_snitch_ideal_cache
      for (genvar t = 0; unsigned'(t) < NumTilesPerGroup; t++) begin: gen_snitch_ideal_cache
        for (genvar c = 0; unsigned'(c) < NumCoresPerTile; c++) begin: gen_snitch_ideal_cache
          addr_t addr;
          data_t data;
          assign addr = dut.i_mempool_cluster.gen_groups[g].i_group.gen_tiles[t].i_tile.i_tile.snitch_inst_addr[c/NumCoresPerCache][c%NumCoresPerCache];
          assign data = dut.l2_mem.sram[addr[L2ByteOffset +: dut.L2AddrWidth]] >> (8 * addr[L2ByteOffset-1:0]);
          assign dut.i_mempool_cluster.gen_groups[g].i_group.gen_tiles[t].i_tile.i_tile.snitch_inst_data[c/NumCoresPerCache][c%NumCoresPerCache] = data;
          assign dut.i_mempool_cluster.gen_groups[g].i_group.gen_tiles[t].i_tile.i_tile.snitch_inst_ready[c/NumCoresPerCache][c%NumCoresPerCache] = '1;
        end
      end
    end
  end

  // TODO read EOC value with DPI

endmodule : mempool_tb_verilator
