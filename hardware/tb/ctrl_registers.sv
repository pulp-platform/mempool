// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

import mempool_pkg::addr_t;

module ctrl_registers #(
    parameter int DataWidth                      = 32   ,
    parameter int NumRegs                        = 0    ,
    parameter addr_t CtrlRegistersBaseAddr       = 0    ,
    parameter addr_t CtrlRegistersEndAddr        = 0    ,
    // Parameters
    parameter logic [DataWidth-1:0] TCDMBaseAddr = 0    ,
    parameter logic [DataWidth-1:0] TCDMSize     = 0    ,
    parameter logic [DataWidth-1:0] NumCores     = 0    ,
    // AXI Structs
    parameter type axi_aw_chan_t                 = logic,
    parameter type axi_w_chan_t                  = logic,
    parameter type axi_b_chan_t                  = logic,
    parameter type axi_ar_chan_t                 = logic,
    parameter type axi_r_chan_t                  = logic,
    parameter type axi_req_t                     = logic,
    parameter type axi_resp_t                    = logic
  ) (
    input  logic                      clk_i,
    input  logic                      rst_ni,
    // AXI Bus
    input  axi_req_t                  axi_slave_req_i ,
    output axi_resp_t                 axi_slave_resp_o,
    // Control registers
    output logic      [DataWidth-1:0] tcdm_start_address_o,
    output logic      [DataWidth-1:0] tcdm_end_address_o,
    output logic      [DataWidth-1:0] num_cores_o
  );

  import mempool_pkg::*;

  /***************
   *   Signals   *
   ***************/

  localparam CtrlRegistersMask = CtrlRegistersEndAddr - CtrlRegistersBaseAddr;

  struct packed {
    logic [DataWidth-1:0] num_cores         ;
    logic [DataWidth-1:0] tcdm_end_address  ;
    logic [DataWidth-1:0] tcdm_start_address;
  } ctrl_regs;

  assign tcdm_start_address_o = ctrl_regs.tcdm_start_address;
  assign tcdm_end_address_o   = ctrl_regs.tcdm_end_address  ;
  assign num_cores_o          = ctrl_regs.num_cores         ;
  assign ctrl_regs            = '{
    tcdm_start_address: TCDMBaseAddr,
    tcdm_end_address  : TCDMSize    ,
    num_cores         : NumCores
  };

  axi_req_t  axi_req;
  axi_resp_t axi_resp;

  /*************
   *  AXI Cut  *
   *************/

  axi_cut #(
    .aw_chan_t(axi_aw_chan_t),
    .w_chan_t (axi_w_chan_t ),
    .b_chan_t (axi_b_chan_t ),
    .ar_chan_t(axi_ar_chan_t),
    .r_chan_t (axi_r_chan_t ),
    .req_t    (axi_req_t    ),
    .resp_t   (axi_resp_t   )
  ) i_axi_cut (
    .clk_i     (clk_i           ),
    .rst_ni    (rst_ni          ),
    .slv_req_i (axi_slave_req_i ),
    .slv_resp_o(axi_slave_resp_o),
    .mst_req_o (axi_req         ),
    .mst_resp_i(axi_resp        )
  );

  /*************************
   *  Read-only registers  *
   *************************/

  always_comb begin
    // Default state
    axi_resp = '0;

    // Always 'ready' to receive write messages
    axi_resp.w_ready = 1'b1;

    // Got a write request
    if (axi_req.aw_valid) begin
      // Send error
      axi_resp.b.id    = axi_req.aw.id        ;
      axi_resp.b.resp  = axi_pkg::RESP_SLVERR ;
      axi_resp.b_valid = 1'b1                 ;
      if (axi_req.b_ready)
        axi_resp.aw_ready = 1'b1;
    end

    // Got a read request
    if (axi_req.ar_valid) begin
      automatic addr_t word_addr = (axi_req.ar.addr & CtrlRegistersMask) >> 2;

      axi_resp.r.id    = axi_req.ar.id;
      axi_resp.r.last  = 1'b1         ;
      axi_resp.r_valid = 1'b1         ;

      if (word_addr >= NumRegs) begin
        // Invalid address
        axi_resp.resp = axi_pkg::RESP_SLVERR;
      end else begin
        axi_resp.data = ctrl_regs[word_addr];
      end

      if (axi_resp.r_ready)
        axi_resp.ar_ready = 1'b1;
    end
  end

  /****************
   *  Assertions  *
   ****************/

  if (($bits(ctrl_regs) / DataWidth) < NumRegs)
    $fatal(1, "[ctrl_registers] Fewer control registers as declared.");

  if (($bits(ctrl_regs) / DataWidth) > NumRegs)
    $fatal(1, "[ctrl_registers] More control registers as declared.");

  if (2**$clog2(CtrlRegistersMask + 1) != CtrlRegistersMask + 1)
    $fatal(1, "[ctrl_registers] The length of the CtrlRegisters memory zone should be a power of two.");

endmodule : ctrl_registers
