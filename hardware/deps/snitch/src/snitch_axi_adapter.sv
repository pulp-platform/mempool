/* Copyright 2018-2019 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:  axi_adapter.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   1.8.2018
 *
 * Description: Manages communication with the AXI Bus
 */

module snitch_axi_adapter #(
  parameter int unsigned WriteFIFODepth = 2,
  parameter type axi_mst_req_t  = logic,
  parameter type axi_mst_resp_t = logic
) (
  input  logic                                clk_i,
  input  logic                                rst_ni,
  // AXI port
  input  axi_mst_resp_t                       axi_resp_i,
  output axi_mst_req_t                        axi_req_o,

  input  logic [$bits(axi_req_o.aw.addr)-1:0] slv_qaddr_i,
  input  logic                                slv_qwrite_i,
  input  logic [3:0]                          slv_qamo_i,
  input  logic [$bits(axi_req_o.w.data)-1:0]  slv_qdata_i,
  input  logic [$bits(axi_req_o.w.strb)-1:0]  slv_qstrb_i,
  input  logic [7:0]                          slv_qrlen_i,
  input  logic [snitch_pkg::ReorderIdWidth-1:0] slv_qid_i,
  input  logic                                slv_qvalid_i,
  output logic                                slv_qready_o,
  output logic [$bits(axi_req_o.w.data)-1:0]  slv_pdata_o,
  output logic [snitch_pkg::ReorderIdWidth-1:0] slv_pid_o,
  output logic                                slv_perror_o,
  output logic                                slv_plast_o,
  output logic                                slv_pvalid_o,
  input  logic                                slv_pready_i
);

  typedef enum logic [3:0] {
    AMONone = 4'h0,
    AMOSwap = 4'h1,
    AMOAdd  = 4'h2,
    AMOAnd  = 4'h3,
    AMOOr   = 4'h4,
    AMOXor  = 4'h5,
    AMOMax  = 4'h6,
    AMOMaxu = 4'h7,
    AMOMin  = 4'h8,
    AMOMinu = 4'h9,
    AMOLR   = 4'hA,
    AMOSC   = 4'hB
  } amo_op_t;

  typedef struct packed {
    logic [$bits(axi_req_o.w.data)-1:0] data;
    logic [$bits(axi_req_o.w.strb)-1:0] strb;
  } write_t;

  logic   write_full;
  logic   write_empty;
  write_t write_data_in;
  write_t write_data_out;

  assign axi_req_o.aw.addr   = slv_qaddr_i;
  assign axi_req_o.aw.prot   = 3'b0;
  assign axi_req_o.aw.region = 4'b0;
  assign axi_req_o.aw.size   = $clog2($bits(axi_req_o.w.data)/8);
  assign axi_req_o.aw.len    = '0;
  assign axi_req_o.aw.burst  = axi_pkg::BURST_INCR;
  assign axi_req_o.aw.lock   = 1'b0;
  assign axi_req_o.aw.cache  = 4'b0;
  assign axi_req_o.aw.qos    = 4'b0;
  assign axi_req_o.aw.id     = slv_qid_i;
  assign axi_req_o.aw.user   = '0;
  assign axi_req_o.aw_valid  = ~write_full & slv_qvalid_i & slv_qwrite_i;


  always_comb begin
    write_data_in.data = slv_qdata_i;
    write_data_in.strb = slv_qstrb_i;
    unique case (amo_op_t'(slv_qamo_i))
      // RISC-V atops have a load semantic
      AMOSwap: axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_ATOMICSWAP};
      AMOAdd:  axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_ADD};
      AMOAnd:  begin
        // in this case we need to invert the data to get a "CLR"
        write_data_in.data = ~slv_qdata_i;
        axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_CLR};
      end
      AMOOr:   axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SET};
      AMOXor:  axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_EOR};
      AMOMax:  axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SMAX};
      AMOMaxu: axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_UMAX};
      AMOMin:  axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_SMIN};
      AMOMinu: axi_req_o.aw.atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_LITTLE_END, axi_pkg::ATOP_UMIN};
      default: axi_req_o.aw.atop = '0;
    endcase
  end

  fifo_v3 #(
    .DEPTH      ( WriteFIFODepth                             ),
    .dtype      ( write_t                                    )
  ) i_fifo_v3 (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0                                       ),
    .testmode_i ( 1'b0                                       ),
    .full_o     ( write_full                                 ),
    .empty_o    ( write_empty                                ),
    .usage_o    ( /* NC */                                   ),
    .data_i     ( write_data_in                              ),
    .push_i     ( slv_qvalid_i & slv_qready_o & slv_qwrite_i ),
    .data_o     ( write_data_out                             ),
    .pop_i      ( axi_req_o.w_valid & axi_resp_i.w_ready     )
  );

  assign axi_req_o.w.data    = write_data_out.data;
  assign axi_req_o.w.strb    = write_data_out.strb;
  assign axi_req_o.w.last    = 1'b1;
  assign axi_req_o.w.user    = '0;
  assign axi_req_o.w_valid   = ~write_empty;

  assign axi_req_o.b_ready  = 1'b1;

  assign axi_req_o.ar.addr   = slv_qaddr_i;
  assign axi_req_o.ar.prot   = 3'b0;
  assign axi_req_o.ar.region = 4'b0;
  assign axi_req_o.ar.size   = $clog2($bits(axi_req_o.w.data)/8);
  assign axi_req_o.ar.len    = slv_qrlen_i;
  assign axi_req_o.ar.burst  = axi_pkg::BURST_INCR;
  assign axi_req_o.ar.lock   = 1'b0;
  assign axi_req_o.ar.cache  = 4'b0;
  assign axi_req_o.ar.qos    = 4'b0;
  assign axi_req_o.ar.id     = slv_qid_i;
  assign axi_req_o.ar.user   = '0;
  assign axi_req_o.ar_valid  = slv_qvalid_i & ~slv_qwrite_i;

  assign slv_pdata_o       = axi_resp_i.r.data;
  assign slv_pid_o         = axi_resp_i.r.id;
  assign slv_perror_o      = (axi_resp_i.r.resp inside {axi_pkg::RESP_EXOKAY, axi_pkg::RESP_OKAY}) ? 1'b0 : 1'b1;
  assign slv_plast_o       = axi_resp_i.r.last;
  assign slv_pvalid_o      = axi_resp_i.r_valid;
  assign axi_req_o.r_ready = slv_pready_i;

  assign slv_qready_o = (axi_resp_i.ar_ready & axi_req_o.ar_valid)
                      | (axi_resp_i.aw_ready & axi_req_o.aw_valid);

  // pragma translate_off
  hot_one : assert property (
    @(posedge clk_i) disable iff (!rst_ni) (slv_qvalid_i & slv_qwrite_i & slv_qready_o) |-> (slv_qrlen_i == 0))
      else $warning("Bursts are not supported for write transactions");
  // pragma translate_on
endmodule
