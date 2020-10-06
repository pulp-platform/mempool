// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "common_cells/registers.svh"
import mempool_pkg::addr_t;

module ctrl_registers #(
    parameter int DataWidth                      = 32,
    parameter int NumRegs                        = 0,
    // Parameters
    parameter logic [DataWidth-1:0] TCDMBaseAddr = 0,
    parameter logic [DataWidth-1:0] TCDMSize     = 0,
    parameter logic [DataWidth-1:0] NumCores     = 0,
    // AXI Structs
    parameter type axi_lite_req_t                = logic,
    parameter type axi_lite_resp_t               = logic
  ) (
    input  logic                           clk_i,
    input  logic                           rst_ni,
    // AXI Bus
    input  axi_lite_req_t                  axi_lite_slave_req_i,
    output axi_lite_resp_t                 axi_lite_slave_resp_o,
    // Control registers
    output logic      [DataWidth-1:0]      tcdm_start_address_o,
    output logic      [DataWidth-1:0]      tcdm_end_address_o,
    output logic      [DataWidth-1:0]      num_cores_o,
    output logic      [NumCores-1:0]       wake_up_o
  );

  import mempool_pkg::*;

  /*****************
   *  Definitions  *
   *****************/

  localparam int unsigned DataWidthInBytes = (DataWidth + 7) / 8;
  localparam int unsigned RegNumBytes      = NumRegs * DataWidthInBytes;
  localparam int unsigned RegDataWidth     = NumRegs * DataWidth;

  localparam logic [DataWidthInBytes-1:0] ReadOnlyReg  = {DataWidthInBytes{1'b1}};
  localparam logic [DataWidthInBytes-1:0] ReadWriteReg = {DataWidthInBytes{1'b0}};

  // Memory map
  // [3:0]:  tcdm_start_address (ro)
  // [7:4]:  tcdm_end_address   (ro)
  // [11:8]: num_cores          (ro)
  // [15:12]:wake_up            (rw)
localparam logic [NumRegs-1:0][DataWidth-1:0] RegRstVal = '{
    {DataWidth{1'b0}},
    NumCores,
    TCDMBaseAddr + TCDMSize,
    TCDMBaseAddr
  };
  localparam logic [NumRegs-1:0][DataWidthInBytes-1:0] AxiReadOnly = '{
    ReadWriteReg,
    ReadOnlyReg,
    ReadOnlyReg,
    ReadOnlyReg
  };

  /***************
   *  Registers  *
   ***************/

  logic [DataWidth-1:0]   tcdm_start_address;
  logic [DataWidth-1:0]   tcdm_end_address;
  logic [DataWidth-1:0]   num_cores;
  logic [DataWidth-1:0]   wake_up;
  logic [RegNumBytes-1:0] wr_active_d;
  logic [RegNumBytes-1:0] wr_active_q;
  
  axi_lite_regs #(
    .RegNumBytes (RegNumBytes               ),
    .AxiAddrWidth(AddrWidth                 ),
    .AxiDataWidth(DataWidth                 ),
    .AxiReadOnly (AxiReadOnly               ),
    .RegRstVal   (RegRstVal                 ),
    .req_lite_t  (axi_lite_req_t            ),
    .resp_lite_t (axi_lite_resp_t           )
  ) i_axi_lite_regs (
    .clk_i      (clk_i                                                     ),
    .rst_ni     (rst_ni                                                    ),
    .axi_req_i  (axi_lite_slave_req_i                                      ),
    .axi_resp_o (axi_lite_slave_resp_o                                     ),
    .wr_active_o(wr_active_d                                               ),
    .rd_active_o(/* Unused */                                              ),
    .reg_d_i    ('0                                                        ),
    .reg_load_i ('0                                                        ),
    .reg_q_o    ({wake_up, num_cores, tcdm_end_address, tcdm_start_address})
  );

  /***************
   *   Signals   *
   ***************/

  assign tcdm_start_address_o = tcdm_start_address;
  assign tcdm_end_address_o   = tcdm_end_address;
  assign num_cores_o          = num_cores;

  // converts 32 bit wake up to 256 bit
  always_comb begin
    wake_up_o = '0;
    if (wr_active_q[15:12]) begin
      if (wake_up < NumCores) begin
        wake_up_o = 1 << wake_up;
      end else if (wake_up == {DataWidth{1'b1}}) begin
        wake_up_o = {NumCores{1'b1}};
      end
    end
  end

  // register to add +1 latency to the wr_active signal
  `FF(wr_active_q, wr_active_d, rst_ni)

endmodule : ctrl_registers
