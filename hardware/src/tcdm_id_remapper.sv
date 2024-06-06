// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Description: Merges N parallel TCDM requests into a single flow.
//
// Author: Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

module tcdm_id_remapper
  import mempool_pkg::*;
  import snitch_pkg::MetaIdWidth;
  import snitch_pkg::RobDepth;
  #(
    parameter int unsigned NumIn = 1
  ) (
    input  logic                         clk_i,
    input  logic                         rst_ni,
    // Master side
    input  snitch_pkg::dreq_t            [NumIn-1:0] req_i,
    input  logic                         [NumIn-1:0] req_valid_i,
    output logic                         [NumIn-1:0] req_ready_o,
    output snitch_pkg::dresp_t           [NumIn-1:0] resp_o,
    output logic                         [NumIn-1:0] resp_valid_o,
    input  logic                         [NumIn-1:0] resp_ready_i,
    // Slave side
    output snitch_pkg::dreq_t            req_o,
    output logic                         req_valid_o,
    input  logic                         req_ready_i,
    input  snitch_pkg::dresp_t           resp_i,
    input  logic                         resp_valid_i,
    output logic                         resp_ready_o
  );

`include "common_cells/registers.svh"

  if (NumIn == 1) begin: gen_single_port
    assign req_o       = req_i;
    assign req_valid_o = req_valid_i;
    assign req_ready_o = req_ready_i;

    assign resp_o       = resp_i;
    assign resp_valid_o = resp_valid_i;
    assign resp_ready_o = resp_ready_i;
  end: gen_single_port else begin: gen_remapper
    snitch_pkg::dreq_t req;
    logic req_valid;
    logic req_ready;

    meta_id_t next_id;
    logic no_free_id;

    // Lock the output id if the request has not been taken yet
    logic id_lock_d, id_lock_q;

    typedef logic [cf_math_pkg::idx_width(NumIn)-1:0] id_t;
    id_t id;

    meta_id_t [RobDepth-1:0] remapped_id_q, remapped_id_d;
    logic [RobDepth-1:0] remapped_id_valid_q, remapped_id_valid_d;
    id_t [RobDepth-1:0] id_q, id_d;

    `FF(remapped_id_q, remapped_id_d, '0)
    `FF(remapped_id_valid_q, remapped_id_valid_d, '0)
    `FF(id_q, id_d, '0)
    `FF(id_lock_q, id_lock_d, '0)

    lzc #(
      .WIDTH(RobDepth)
    ) i_next_id_lzc (
      .in_i   (~remapped_id_valid_q),
      .cnt_o  (next_id             ),
      .empty_o(no_free_id          )
    );

    always_comb begin
      // Maintain state
      remapped_id_d       = remapped_id_q;
      remapped_id_valid_d = remapped_id_valid_q;
      id_d                = id_q;
      id_lock_d           = id_lock_q;

      if (req_valid_o && !req_ready_i) begin
        // valid but not ready, we need to keep the id unchanged
        id_lock_d         = 1'b1;
      end

      // Did we get a new request?
      if (req_valid_o && req_ready_i) begin
        if (id_lock_q) begin
          // the outstanding ID is already stored in req
          remapped_id_d[req.id]        = req.id;
          remapped_id_valid_d[req.id]  = 1'b1;
          id_d[req.id]                 = id;
          id_lock_d                    = 1'b0;
        end else begin
          remapped_id_d[next_id]       = req.id;
          remapped_id_valid_d[next_id] = 1'b1;
          id_d[next_id]                = id;
        end
      end

      // Did we sent a new response?
      if (resp_valid_i && resp_ready_o)
        remapped_id_valid_d[resp_i.id] = 1'b0;
    end

    ///////////////
    //  Request  //
    ///////////////

    rr_arb_tree #(
      .NumIn     (NumIn           ),
      .DataType  (snitch_pkg::dreq_t),
      .AxiVldRdy (1'b1            ),
      .LockIn    (1'b1            )
    ) i_arbiter (
      .clk_i  (clk_i      ),
      .rst_ni (rst_ni     ),
      .flush_i(1'b0       ),
      .rr_i   ('0         ),
      .req_i  (req_valid_i),
      .gnt_o  (req_ready_o),
      .data_i (req_i      ),
      .gnt_i  (req_ready  ),
      .req_o  (req_valid  ),
      .data_o (req        ),
      .idx_o  (id         )
    );

    always_comb begin
      // Ready if upstream is ready and we have a free id
      req_valid_o = req_valid && !no_free_id;
      req_ready   = req_ready_i && !no_free_id;

      // Forward the request
      req_o    = req;
      if (!id_lock_q)
        req_o.id = next_id;
    end

    ////////////////
    //  Response  //
    ////////////////

    stream_demux #(
      .N_OUP(NumIn)
    ) i_response_demux (
      .inp_valid_i(resp_valid_i   ),
      .inp_ready_o(resp_ready_o   ),
      .oup_sel_i  (id_q[resp_i.id]),
      .oup_ready_i(resp_ready_i   ),
      .oup_valid_o(resp_valid_o   )
    );

    always_comb begin
      for (int i = 0; i < NumIn; i++) begin
        resp_o[i]    = resp_i;
        resp_o[i].id = remapped_id_q[resp_i.id];
      end
    end
  end: gen_remapper

endmodule: tcdm_id_remapper
