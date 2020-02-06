// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module ctrl_registers #(
    parameter int unsigned TCDMSize = 0,
    parameter int unsigned NumCores = 0
  ) (
    input         logic        clk_i,
    input         logic        rst_ni,
    // APB Bus
    AXI_BUS.Slave              slave,
    // Control registers
    output        logic [31:0] tcdm_start_address_o,
    output        logic [31:0] tcdm_end_address_o,
    output        logic [31:0] num_cores_o
  );

  import mempool_pkg::*;

  /***************
   *   Signals   *
   ***************/

  struct packed {
    logic [31:0] num_cores         ;
    logic [31:0] tcdm_end_address  ;
    logic [31:0] tcdm_start_address;
  } ctrl_regs_init, ctrl_regs_q;

  assign tcdm_start_address_o = ctrl_regs_q.tcdm_start_address;
  assign tcdm_end_address_o   = ctrl_regs_q.tcdm_end_address  ;
  assign num_cores_o          = ctrl_regs_q.num_cores         ;
  assign ctrl_regs_init       = '{
    tcdm_start_address: '0      ,
    tcdm_end_address  : TCDMSize,
    num_cores         : NumCores
  };

  /***************
   *   RW REGS   *
   ***************/

  /*apb_rw_regs #(
    .N_REGS(3)
  ) i_apb_soc_registers (
    .pclk_i   ( clk_i                ),
    .preset_ni( rst_ni               ),
    .paddr_i  ( apb.paddr & 16'hFFFF ),
    .penable_i( apb.penable          ),
    .pprot_i  ( apb.pprot            ),
    .prdata_o ( apb.prdata           ),
    .pready_o ( apb.pready           ),
    .psel_i   ( apb.psel             ),
    .pslverr_o( apb.pslverr          ),
    .pstrb_i  ( apb.pstrb            ),
    .pwdata_i ( apb.pwdata           ),
    .pwrite_i ( apb.pwrite           ),
    .init_i   ( ctrl_regs_init       ),
    .q_o      ( ctrl_regs_q          )
    );*/

endmodule : ctrl_registers
