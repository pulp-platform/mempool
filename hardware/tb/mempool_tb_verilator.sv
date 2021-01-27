// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

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

  `ifdef NUM_CORES
  localparam NumCores = `NUM_CORES;
  `else
  localparam NumCores = 256;
  `endif

  `ifdef BOOT_ADDR
  localparam BootAddr = `BOOT_ADDR;
  `else
  localparam BootAddr = 0;
  `endif

  localparam        BankingFactor    = 4;
  localparam addr_t TCDMBaseAddr     = '0;
  localparam        TCDMSizePerBank  = 1024 /* [B] */;
  localparam        NumTiles         = NumCores / NumCoresPerTile;
  localparam        NumTilesPerGroup = NumTiles / NumGroups;
  localparam        NumBanks         = NumCores * BankingFactor;
  localparam        TCDMSize         = NumBanks * TCDMSizePerBank;

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

  logic fetch_en;
  logic eoc_valid;

  axi_system_req_t  axi_mst_req;
  axi_system_resp_t axi_mst_resp;

  /*********
   *  DUT  *
   *********/

  mempool_system #(
    .NumCores       (NumCores     ),
    .BankingFactor  (BankingFactor),
    .TCDMBaseAddr   (TCDMBaseAddr ),
    .BootAddr       (BootAddr     )
  ) dut (
    .clk_i          (clk          ),
    .rst_ni         (rst_n        ),
    .fetch_en_i     (fetch_en     ),
    .eoc_valid_o    (eoc_valid    ),
    .busy_o         (/*Unused*/   ),
    .mst_req_o      (axi_mst_req  ),
    .mst_resp_i     (axi_mst_resp ),
    .slv_req_i      (/*Unused*/ '0),
    .slv_resp_o     (/*Unused*/   ),
    .rab_conf_req_i ('0           ),
    .rab_conf_resp_o(/*Unused*/   )
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

  // TODO read EOC value with DPI

endmodule : mempool_tb_verilator
