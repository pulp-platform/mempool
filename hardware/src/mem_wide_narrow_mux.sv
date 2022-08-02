// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Thomas Benz <tbenz@iis.ee.ethz.ch>
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"

/// This module multiplexes many narrow ports and one wide port onto many narrow
/// ports. The wide or narrow ports can be selected by using the `sel_wide_i` signal.
///
/// `1` selects the wide port.
/// `0` selects the narrow port.
///
/// ## Constraint
///
/// The data and strb width of the wide port must be evenly divisible by the
/// small port data and strb width.
///
/// ## Caution
///
/// As of now this module's request always need an immediate grant in case
/// `sel_wide_i` is high. Any delayed grant will break the module's behavior.
module mem_wide_narrow_mux #(
  /// Width of narrow data.
  parameter int unsigned NarrowDataWidth = 0,
  /// Width of wide data.
  parameter int unsigned WideDataWidth   = 0,
  /// Request type of narrow inputs.
  parameter type slv_narrow_req_t        = logic,
  /// Response type of narrow inputs.
  parameter type slv_narrow_rsp_t        = logic,
  /// Request type of wide inputs.
  parameter type slv_wide_req_t          = logic,
  /// Response type of wide inputs.
  parameter type slv_wide_rsp_t          = logic,
  /// Request type of wide inputs.
  parameter type slv_narrow_req_t        = logic,
  /// Response type of wide inputs.
  parameter type slv_narrow_rsp_t        = logic,
  /// Derived. *Do not override*
  /// Number of narrow inputs.
  parameter int unsigned NrPorts = WideDataWidth / NarrowDataWidth
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  // Inputs
  /// Narrow side.
  input  slv_narrow_req_t [NrPorts-1:0] in_narrow_req_i,
  input  logic            [NrPorts-1:0] in_narrow_req_valid_i,
  output logic            [NrPorts-1:0] in_narrow_req_ready_o,
  output slv_narrow_rsp_t [NrPorts-1:0] in_narrow_rsp_o,
  output logic            [NrPorts-1:0] in_narrow_rsp_valid_o,
  input  logic            [NrPorts-1:0] in_narrow_rsp_ready_i,
  /// Wide side.
  input  slv_wide_req_t                 in_wide_req_i,
  input  logic                          in_wide_req_valid_i,
  output logic                          in_wide_req_ready_o,
  output slv_wide_rsp_t                 in_wide_rsp_o,
  output logic                          in_wide_rsp_valid_o,
  input  logic                          in_wide_rsp_ready_i,
  // Multiplexed output.
  output mst_narrow_req_t [NrPorts-1:0] out_req_o,
  output logic            [NrPorts-1:0] out_req_wide_o,
  output logic            [NrPorts-1:0] out_req_valid_o,
  input  logic            [NrPorts-1:0] out_req_ready_i,
  input  mst_narrow_rsp_t [NrPorts-1:0] out_rsp_i,
  input  logic            [NrPorts-1:0] out_rsp_wide_i,
  input  logic            [NrPorts-1:0] out_rsp_valid_i,
  output logic            [NrPorts-1:0] out_rsp_ready_o,
  /// `0`: Use narrow port, `1`: Use wide port
  input  logic                          sel_wide_i
);

  localparam int unsigned NarrowBeWidth = NarrowDataWidth/8;

  // Reductions
  logic [NrPorts-1:0] in_wide_req_ready;
  logic [NrPorts-1:0] in_wide_rsp_valid;
  assign in_wide_req_ready_o = &in_wide_req_ready;
  assign in_wide_rsp_valid_o = &in_wide_rsp_valid;

  always_comb begin
    // ----------------
    // Backward Channel
    // ----------------
    in_narrow_rsp_valid_o = '0;
    in_wide_rsp_valid     = '0;
    for (int i = 0; i < NrPorts; i++) begin
      in_narrow_rsp_o[i] = out_rsp_i[i];
      if (out_rsp_wide_i[i]) begin
        in_wide_rsp_valid = out_rsp_valid_i;
      end else begin
        in_narrow_rsp_valid_o = out_rsp_valid_i;
      end
      // Broadcast data from all banks.
      in_wide_rsp_o.ini_addr = '0;
      in_wide_rsp_o.rdata[i*NarrowDataWidth+:NarrowDataWidth] = out_rsp_i[i].rdata;
      in_wide_rsp_valid = out_rsp_valid_i;
    end

    // ---------------
    // Forward Channel
    // ---------------
    // By default feed through narrow requests.
    out_req_o             = in_narrow_req_i;
    out_req_wide_o        = '0
    out_req_valid_o       = in_narrow_req_valid_i;
    in_narrow_req_ready_o = out_req_ready_i;
    // Tie-off wide by default.
    in_wide_req_ready     = '0;

    // The wide port is selected.
    if (sel_wide_i) begin
      for (int i = 0; i < NrPorts; i++) begin
        out_req_valid_o[i] = in_wide_req_valid_i;
        // Block access from narrow ports.
        in_narrow_req_ready_o[i] = 1'b0;
        out_req_o[i] = '{
          wdata: in_wide_req_i.wdata[i*NarrowDataWidth+:NarrowDataWidth],
          wen: in_wide_req_i.wen,
          be: in_wide_req_i.be[i*NarrowBeWidth+:NarrowBeWidth],
          tgt_addr: in_wide_req_i.tgt_addr,
          ini_addr: in_wide_req_i.ini_addr,
        };
        // The protocol requires that the response is always granted
        // immediately (at least when `sel_wide_i` is high).
        in_wide_req_ready = out_req_ready_i;
      end
    end
  end

  // ----------
  // Assertions
  // ----------
  `ASSERT_INIT(DataDivisble, WideDataWidth % NarrowDataWidth  == 0)

  // Currently the module has a couple of `quirks` and interface requirements
  // which are checked here.
  logic [NrPorts-1:0] q_valid_flat;
  logic [NrPorts-1:0][NarrowDataWidth-1:0] q_data;
  logic [NrPorts-1:0][NarrowBeWidth-1:0] q_strb;

  `ASSERT(ImmediateGrantWide, in_wide_req_i.q_valid |-> in_wide_rsp_o.q_ready)
  for (genvar i = 0; i < NrPorts; i++) begin : gen_per_port
    assign q_valid_flat[i] = out_req_o[i].q_valid;
    assign q_data[i] = out_req_o[i].q.data;
    assign q_strb[i] = out_req_o[i].q.strb;
    `ASSERT(ImmediateGrantOut, sel_wide_i & out_req_o[i].q_valid |-> out_rsp_i[i].q_ready)
    `ASSERT(SilentNarrow, sel_wide_i |-> !in_narrow_rsp_o[i].q_ready)
    `ASSERT(NarrowPassThrough, !sel_wide_i & in_narrow_req_i[i].q_valid |-> out_req_o[i].q_valid)
  end
  `ASSERT(DmaSelected, sel_wide_i & in_wide_req_i.q_valid |-> &q_valid_flat)
  `ASSERT(DmaSelectedReadyWhenValid,
    sel_wide_i & in_wide_req_i.q_valid |-> in_wide_rsp_o.q_ready)
  `ASSERT(DMAWriteDataCorrect,
    in_wide_req_i.q_valid & in_wide_rsp_o.q_ready |->
    (in_wide_req_i.q.data == q_data) && (in_wide_req_i.q.strb == q_strb))

endmodule
