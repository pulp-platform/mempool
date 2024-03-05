// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Diyou Shen ETH Zurich


module burst_cutter #(
  parameter int unsigned      NrCut           = 0,
  parameter int unsigned      AddrWidth       = 32,
  parameter int unsigned      ByteOffset      = 2,
  parameter int unsigned      NumTiles        = 2,
  parameter int unsigned      CutLen          = 2,
  parameter int unsigned      BLenWidth       = 1,

  parameter type              tcdm_breq_t     = logic,
  parameter type              meta_id_t       = logic,
  // Dependency paramter, do not overwrite
  parameter type              tile_id_t       = logic [$clog2(NumTiles)-1:0]
) (
  input  logic                clk_i,
  input  logic                rst_ni,
  // Memory Request In
  input  logic       [31:0]   req_addr_i,
  input  logic                req_write_i,
  input  logic       [3:0]    req_amo_i,
  input  logic       [31:0]   req_data_i,
  input  logic       [3:0]    req_strb_i,
  input  meta_id_t            req_id_i,
  input  tcdm_breq_t          req_burst_i,
  input  logic                req_valid_i,
  output logic                req_ready_o,
  // Memory Request Out
  output logic       [31:0]   req_addr_o,
  output logic                req_write_o,
  output logic       [3:0]    req_amo_o,
  output logic       [31:0]   req_data_o,
  output logic       [3:0]    req_strb_o,
  output meta_id_t            req_id_o,
  output tcdm_breq_t          req_burst_o,
  output logic                req_valid_o,
  input  logic                req_ready_i
);
  typedef enum logic {
    // normal requests, first cut of burst
    Bypass,
    // second cut of burst
    BurstCut
  } burst_cutter_fsm_e;

  localparam int unsigned BankOffsetBits  = $clog2(CutLen);
  localparam int unsigned ConstantBitsLSB = ByteOffset + BankOffsetBits;
  localparam int unsigned TileBankLen     = (1 << BankOffsetBits);

  localparam int unsigned N_FU = spatz_pkg::N_FU;

  // FSM state
  burst_cutter_fsm_e  state_d, state_q;
  // FSM stored signals
  logic [31:0]        cut_addr_d,  cut_addr_q;
  meta_id_t           cut_id_d,    cut_id_q;
  tcdm_breq_t         cut_burst_d, cut_burst_q;

  logic [BankOffsetBits-1:0] bank_offset;
  logic [BLenWidth:0]        max_blen;
  logic [BLenWidth:0]        remaining_len;
  burst_cutter_fsm_e  next_state;

  always_ff @(posedge clk_i or negedge rst_ni) begin : burst_cutter_proc
    if(~rst_ni) begin
      state_q     <= Bypass;
      cut_burst_q <= '0;
      cut_addr_q  <= '0;
      cut_id_q    <= '0;
    end else begin
      state_q     <= state_d;
      cut_burst_q <= cut_burst_d;
      cut_addr_q  <= cut_addr_d;
      cut_id_q    <= cut_id_d;
    end
  end

  if (NrCut == 0) begin
    // No cut, bypass all the signals
    assign req_addr_o    = req_addr_i;
    assign req_write_o   = req_write_i;
    assign req_amo_o     = req_amo_i;
    assign req_data_o    = req_data_i;
    assign req_strb_o    = req_strb_i;
    assign req_id_o      = req_id_i;
    assign req_burst_o   = req_burst_i;
    assign req_valid_o   = req_valid_i;
    assign req_ready_o   = req_ready_i;

    assign state_d       = Bypass;
    assign cut_burst_d   = '0;
    assign cut_addr_d    = '0;
    assign cut_id_d      = '0;
  end else begin
    always_comb begin
      // FSM defaults
      state_d       = state_q;
      cut_burst_d   = cut_burst_q;
      cut_addr_d    = cut_addr_q;
      cut_id_d      = cut_id_q;

      bank_offset   = '0;
      max_blen      = '0;
      remaining_len = '0;

      next_state    = Bypass;

      // Need to cut, use FSM to realize the logic
      case (state_q)
        Bypass: begin
          // Bypass the signals
          req_addr_o    = req_addr_i;
          req_write_o   = req_write_i;
          req_amo_o     = req_amo_i;
          req_data_o    = req_data_i;
          req_strb_o    = req_strb_i;
          req_id_o      = req_id_i;
          req_burst_o   = req_burst_i;
          req_valid_o   = req_valid_i;
          req_ready_o   = req_ready_i;

          // Keep current state by default
          next_state    = state_q;

          // Check if it is valid and being a burst request
          if (req_burst_i.burst & req_valid_i) begin
            bank_offset   = req_addr_i[ConstantBitsLSB-1 : ByteOffset];
            max_blen      = TileBankLen - bank_offset;
            if (req_write_i) begin
              // no support for write burst, tie to 0
              req_burst_o = '0;
            end else begin
              // read burst, check region
              // if not cross bank, bypass using previous assignments
              if (req_burst_i.blen > max_blen) begin
                next_state = BurstCut;

                // pause taking in new requests
                req_ready_o = 1'b0;
                // Send out the first burst
                req_burst_o   = '{
                  burst : 1'b1,
                  blen  : max_blen
                };
                remaining_len = req_burst_i.blen - max_blen;
                // store the info for next burst
                cut_burst_d   = '{
                  burst : 1'b1,
                  blen  : remaining_len
                };
                cut_addr_d    = req_addr_i + (max_blen << ByteOffset);
                // calculate the next ID, can rollover (ROB should handle it)
                cut_id_d      = req_id_i + max_blen;
              end
            end
          end

          if (req_ready_i) begin
            // Keep state until the current one is picked
            state_d = next_state;
          end
        end

        BurstCut: begin
          next_state = state_q;
          // assign the outputs
          // send out this part and wait for ready
          req_addr_o    = cut_addr_q;
          req_write_o   = '0;           // only read burst is supported
          req_amo_o     = '0;           // no atomic supported for burst
          req_data_o    = '0;
          req_strb_o    = '0;
          req_id_o      = cut_id_q;     // use new calculated id
          req_burst_o   = cut_burst_q;
          req_valid_o   = 1'b1;
          req_ready_o   = 1'b0;

          if (req_ready_i) begin
            // we got the ready, the second part is out
            next_state    = Bypass;
            req_ready_o   = req_ready_i;
          end

          state_d = next_state;
        end

        default: state_d = Bypass;
      endcase
    end
  end

  /******************
   *   Assertions   *
   ******************/
  // Check number of cuts.
  if (NrCut > 1)
    $error("[burst_cutter] Only support one/zero-cut currently");
endmodule : burst_cutter
