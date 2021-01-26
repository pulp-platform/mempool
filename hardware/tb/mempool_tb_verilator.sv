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

  /*********
   *  DUT  *
   *********/

  logic fetch_en;
  logic eoc_valid;

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

  /*****************
   *  Host Memory  *
   *****************/
  `AXI_LITE_TYPEDEF_AW_CHAN_T(axi_lite_aw_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(axi_lite_w_t, axi_data_t, axi_strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(axi_lite_b_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(axi_lite_ar_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(axi_lite_r_t, axi_data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, axi_lite_aw_t, axi_lite_w_t, axi_lite_ar_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_lite_resp_t, axi_lite_b_t, axi_lite_r_t)

  axi_system_req_t  axi_req;
  axi_system_resp_t axi_resp;
  axi_lite_req_t    axi_lite_req;
  axi_lite_resp_t   axi_lite_resp;
  logic             wr_active_d, wr_active_q;

  axi_to_axi_lite #(
    .AxiAddrWidth   (AddrWidth        ),
    .AxiDataWidth   (AxiDataWidth     ),
    .AxiIdWidth     (AxiSystemIdWidth ),
    .AxiUserWidth   (1                ),
    .AxiMaxReadTxns (1                ),
    .AxiMaxWriteTxns(1                ),
    .FallThrough    (1'b0             ),
    .full_req_t     (axi_system_req_t ),
    .full_resp_t    (axi_system_resp_t),
    .lite_req_t     (axi_lite_req_t   ),
    .lite_resp_t    (axi_lite_resp_t  )
  ) i_axi_to_axi_lite (
    .clk_i     (clk          ),
    .rst_ni    (rst_n        ),
    .test_i    (1'b0         ),
    .slv_req_i (axi_req      ),
    .slv_resp_o(axi_resp     ),
    .mst_req_o (axi_lite_req ),
    .mst_resp_i(axi_lite_resp)
  );

  axi_lite_regs #(
    .RegNumBytes (AxiDataWidth/8 ),
    .AxiAddrWidth(AddrWidth      ),
    .AxiDataWidth(AxiDataWidth   ),
    .AxiReadOnly ('0             ),
    .RegRstVal   ('0             ),
    .req_lite_t  (axi_lite_req_t ),
    .resp_lite_t (axi_lite_resp_t)
  ) i_axi_lite_regs (
    .clk_i      (clk          ),
    .rst_ni     (rst_n        ),
    .axi_req_i  (axi_lite_req ),
    .axi_resp_o (axi_lite_resp),
    .wr_active_o(wr_active_d  ),
    .rd_active_o(/*unused*/   ),
    .reg_d_i    ('0           ),
    .reg_load_i ('0           ),
    .reg_q_o    (/*unused*/   )
  );

  // TODO Print UART

  /*********
   *  EOC  *
   *********/
  always_ff @(posedge clk) begin
    if (rst_ni && eoc_valid) begin
      $finish;
    end
  end

  // TODO read EOC value with DPI

endmodule : mempool_tb_verilator
