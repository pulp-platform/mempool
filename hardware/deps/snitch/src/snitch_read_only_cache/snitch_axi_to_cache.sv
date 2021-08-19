// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Samuel Riedel <sriedel@iis.ee.ethz.ch>
//
// Adapted from the axi_burst_splitter authored by:
//   Andreas Kurth       <akurth@iis.ee.ethz.ch>
//   Florian Zaruba      <zarubaf@iis.ee.ethz.ch>
//   Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>


/// Convert from AXI to Cache requests and reconstruct response beats on the way back
module snitch_axi_to_cache #(
  // Maximum number of AXI read bursts outstanding at the same time
  parameter int unsigned MaxTxns            = 32'd0,
  // AXI Bus Types
  parameter int unsigned AddrWidth          = 32'd0,
  parameter int unsigned DataWidth          = 32'd0,
  parameter int unsigned IdWidth            = 32'd0,
  parameter int unsigned UserWidth          = 32'd0,
  parameter type         metadata_t         = logic,
  parameter type         req_t              = logic,
  parameter type         resp_t             = logic,
  parameter snitch_icache_pkg::config_t CFG = '0
)(
  input  logic                         clk_i,
  input  logic                         rst_ni,
  // Cache request
  output logic [CFG.FETCH_AW-1:0]      req_addr_o,
  output logic [CFG.META_WIDTH-1:0]    req_meta_o,
  output logic                         req_valid_o,
  input  logic                         req_ready_i,
  // Cache response
  input  logic [CFG.LINE_WIDTH-1:0]    rsp_data_i,
  input  logic                         rsp_error_i,
  input  logic [CFG.ID_WIDTH_RESP-1:0] rsp_id_i,
  input  logic [CFG.META_WIDTH-1:0]    rsp_meta_i,
  input  logic                         rsp_valid_i,
  output logic                         rsp_ready_o,
  // AXI
  input  req_t                         slv_req_i,
  output resp_t                        slv_rsp_o
);

  import cf_math_pkg::idx_width;

  localparam WORD_OFFSET = idx_width(CFG.LINE_WIDTH/CFG.FETCH_DW); // AXI-word offset within cache line

  // AW, W, B channel --> Never used tie off
  assign slv_rsp_o.aw_ready = 1'b0;
  assign slv_rsp_o.w_ready = 1'b0;
  assign slv_rsp_o.b_valid = 1'b0;
  assign slv_rsp_o.b = '0;

  // R Channel
  typedef logic [IdWidth-1:0] id_t;
  id_t  rsp_id;

  // --------------------------------------------------
  // AR Channel
  // --------------------------------------------------
  typedef logic [WORD_OFFSET-1:0] offset_t;

  logic           r_cnt_dec, r_cnt_req, r_cnt_gnt;
  axi_pkg::len_t  r_cnt_len;
  logic           cnt_alloc_req, cnt_alloc_gnt;
  offset_t        ar_offset, r_offset;

  assign ar_offset = slv_req_i.ar.addr[$clog2(CFG.FETCH_DW/8)+:WORD_OFFSET];


  // Store counters
  axi_burst_splitter_table #(
    .MaxTxns    ( MaxTxns  ),
    .IdWidth    ( IdWidth  ),
    .offset_t   ( offset_t )
  ) i_axi_burst_splitter_table (
    .clk_i,
    .rst_ni,
    .alloc_id_i       ( slv_req_i.ar.id  ),
    .alloc_len_i      ( slv_req_i.ar.len ),
    .alloc_offset_i   ( ar_offset        ), //addr[$clog2(CFG.FETCH_DW/8)+:WORD_OFFSET]
    .alloc_req_i      ( cnt_alloc_req    ),
    .alloc_gnt_o      ( cnt_alloc_gnt    ),
    .cnt_id_i         ( rsp_id           ),
    .cnt_len_o        ( r_cnt_len        ),
    .cnt_offset_o     ( r_offset         ),
    .cnt_set_err_i    ( 1'b0             ),
    .cnt_err_o        ( /* unused */     ),
    .cnt_len_dec_i    ( r_cnt_dec        ),
    .cnt_offset_inc_i ( r_cnt_dec        ),
    .cnt_req_i        ( r_cnt_req        ),
    .cnt_gnt_o        ( r_cnt_gnt        )
  );

  typedef struct packed {
    logic [CFG.FETCH_AW-1:0] addr;
    metadata_t               meta;
    axi_pkg::burst_t         burst;
  } chan_t;

  chan_t ax_d, ax_q, ax_o;

  assign req_addr_o = ax_o.addr;
  assign req_meta_o = ax_o.meta;

  enum logic {Idle, Busy} state_d, state_q;
  always_comb begin
    cnt_alloc_req      = 1'b0;
    ax_d               = ax_q;
    state_d            = state_q;
    ax_o               = '0;
    req_valid_o        = 1'b0;
    slv_rsp_o.ar_ready = 1'b0;
    unique case (state_q)
      Idle: begin
        if (slv_req_i.ar_valid && cnt_alloc_gnt) begin
          if (slv_req_i.ar.len == '0) begin // No splitting required -> feed through.
            ax_o.addr       = slv_req_i.ar.addr >> CFG.LINE_ALIGN << CFG.LINE_ALIGN;
            ax_o.meta.id    = slv_req_i.ar.id;
            ax_o.meta.addr  = slv_req_i.ar.addr[0+:CFG.LINE_ALIGN];
            ax_o.meta.len   = slv_req_i.ar.len;
            ax_o.meta.size  = slv_req_i.ar.size;
            ax_o.meta.valid = slv_req_i.ar_valid;
            req_valid_o = 1'b1;
            // As soon as downstream is ready, allocate a counter and acknowledge upstream.
            if (req_ready_i) begin
              cnt_alloc_req      = 1'b1;
              slv_rsp_o.ar_ready = 1'b1;
            end
          end else begin // Splitting required.
            // Store Ax, allocate a counter, and acknowledge upstream.
            ax_d.addr       = slv_req_i.ar.addr >> CFG.LINE_ALIGN << CFG.LINE_ALIGN;
            ax_d.meta.id    = slv_req_i.ar.id;
            ax_d.meta.addr  = slv_req_i.ar.addr[0+:CFG.LINE_ALIGN];
            ax_d.meta.len   = slv_req_i.ar.len;
            ax_d.meta.size  = slv_req_i.ar.size;
            ax_d.meta.valid = slv_req_i.ar_valid;
            ax_d.burst      = slv_req_i.ar.burst;
            cnt_alloc_req = 1'b1;
            slv_rsp_o.ar_ready    = 1'b1;
            // Try to feed first burst through.
            ax_o          = ax_d;
            ax_o.meta.len = '0;
            req_valid_o = 1'b1;
            if (req_ready_i) begin
              // Reduce number of bursts still to be sent by one and increment address.
              ax_d.meta.len--; // TODO multiply by cache line width
              if (ax_d.burst == axi_pkg::BURST_INCR) begin
                ax_d.addr += (1 << ax_d.meta.size); // TODO Will be the cache line width
              end
            end
            state_d = Busy;
          end
        end
      end
      Busy: begin
        // Sent next burst from split.
        ax_o            = ax_q;
        ax_o.meta.len   = '0;
        req_valid_o     = 1'b1;
        if (req_ready_i) begin
          if (ax_q.meta.len == '0) begin
            // If this was the last burst, go back to idle.
            state_d = Idle;
          end else begin
            // Otherwise, continue with the next burst.
            ax_d.meta.len--;
            if (ax_q.burst == axi_pkg::BURST_INCR) begin
              ax_d.addr += (1 << ax_q.meta.size);
            end
          end
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // registers
  `FFARN(ax_q, ax_d, '0, clk_i, rst_ni)
  `FFARN(state_q, state_d, Idle, clk_i, rst_ni)

  // --------------------------------------------------
  // R Channel
  // --------------------------------------------------
  // Cut path
  typedef struct packed {
    logic [CFG.LINE_WIDTH-1:0]    data;
    logic                         error;
    logic [CFG.ID_WIDTH_RESP-1:0] id;
  } rsp_in_t;

  logic rsp_valid_q, rsp_ready_q;
  rsp_in_t rsp_in_d, rsp_in_q;

  assign rsp_in_d.data  = rsp_data_i;
  assign rsp_in_d.error = rsp_error_i;
  assign rsp_in_d.id    = rsp_id_i;

  spill_register #(
    .T      ( rsp_in_t),
    .Bypass ( 1'b0    )
  ) i_cut_rsp_in (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .valid_i ( rsp_valid_i ),
    .ready_o ( rsp_ready_o ),
    .data_i  ( rsp_in_d    ),
    .valid_o ( rsp_valid_q ),
    .ready_i ( rsp_ready_q ),
    .data_o  ( rsp_in_q    )
  );
  // Reconstruct `id` by splitting cache's ID vector into multiple responses
  // rsp_valid_i --> [forward]                                             --> rsp_valid
  // rsp_ready_o <-- [ready if downstream is ready and input ID is onehot] <-- rsp_ready
  // rsp_id_i    --> [from vector to single ID]                            --> rsp_id
  // rsp_data_i  --> [forward]                                             --> rsp_in_q.data
  // rsp_error_i --> [forward]                                             --> rsp_in_q.error
  // rsp_meta_i  --> [forward]                                             --> rsp_in_q.meta
  logic rsp_valid, rsp_ready;
  logic rsp_id_onehot, rsp_id_empty;
  logic [CFG.ID_WIDTH_RESP-1:0] rsp_id_mask, rsp_id_masked;

  assign rsp_ready_q   = (rsp_id_onehot | rsp_id_empty) & rsp_ready;
  assign rsp_valid     = rsp_valid_q; // And not empty?
  assign rsp_id_masked = rsp_in_q.id & ~rsp_id_mask;

  lzc #(
    .WIDTH ( CFG.ID_WIDTH_RESP ),
    .MODE  ( 0                 )
  ) i_lzc (
    .in_i    ( rsp_id_masked ),
    .cnt_o   ( rsp_id        ),
    .empty_o ( rsp_id_empty  )
  );

  onehot #(
    .Width ( CFG.ID_WIDTH_RESP )
  ) i_onehot (
    .d_i         ( rsp_id_masked ),
    .is_onehot_o ( rsp_id_onehot )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_metadata
    if(~rst_ni) begin
      rsp_id_mask <= '0;
    end else begin
      if (rsp_valid && rsp_ready) begin
        // Downstream handshake --> Go to next ID
        rsp_id_mask <= rsp_id_mask | (1 << rsp_id);
      end
      if (rsp_valid_q && rsp_ready_q) begin // Or empty, should be redundant
        // Upstream handshake --> Clear mask
        rsp_id_mask <= '0;
      end
    end
  end


  // Reconstruct `last`, feed rest through.
  logic r_last_d, r_last_q;
  enum logic {RFeedthrough, RWait} r_state_d, r_state_q;

  always_comb begin
    r_cnt_dec         = 1'b0;
    r_cnt_req         = 1'b0;
    r_last_d          = r_last_q;
    r_state_d         = r_state_q;
    rsp_ready         = 1'b0;
    slv_rsp_o.r.id    = rsp_id;
    slv_rsp_o.r.data  = rsp_in_q.data >> (r_offset * CFG.FETCH_DW);
    slv_rsp_o.r.resp  = rsp_in_q.error; // This response is already an AXI response.
    // slv_rsp_o.r.last  = ~(|metadata[rsp_id].len);
    slv_rsp_o.r.user  = '0;
    slv_rsp_o.r.last  = 1'b0;
    slv_rsp_o.r_valid = 1'b0;
    // slv_rsp_o.r_valid = ~in_rsp_empty;

    unique case (r_state_q)
      RFeedthrough: begin
        // If downstream has an R beat and the R counters can give us the remaining length of
        // that burst, ...
        if (rsp_valid) begin
          r_cnt_req = 1'b1;
          if (r_cnt_gnt) begin
            r_last_d = (r_cnt_len == 8'd0);
            slv_rsp_o.r.last   = r_last_d;
            // Decrement the counter.
            r_cnt_dec         = 1'b1;
            // Try to forward the beat upstream.
            slv_rsp_o.r_valid  = 1'b1;
            if (slv_req_i.r_ready) begin
              // Acknowledge downstream.
              rsp_ready       = 1'b1;
            end else begin
              // Wait for upstream to become ready.
              r_state_d = RWait;
            end
          end
        end
      end
      RWait: begin
        slv_rsp_o.r.last   = r_last_q;
        slv_rsp_o.r_valid  = rsp_valid;
        if (rsp_valid && slv_req_i.r_ready) begin
          rsp_ready       = 1'b1;
          r_state_d         = RFeedthrough;
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // --------------------------------------------------
  // Flip-Flops
  // --------------------------------------------------
  `FFARN(r_last_q, r_last_d, 1'b0, clk_i, rst_ni)
  `FFARN(r_state_q, r_state_d, RFeedthrough, clk_i, rst_ni)

endmodule

































/// Internal module of [`axi_burst_splitter`](module.axi_burst_splitter) to order transactions.
module axi_burst_splitter_table #(
  parameter int unsigned MaxTxns    = 0,
  parameter int unsigned IdWidth    = 0,
  parameter type         offset_t   = logic,
  parameter type         id_t       = logic [IdWidth-1:0]
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  input  id_t           alloc_id_i,
  input  axi_pkg::len_t alloc_len_i,
  input  offset_t       alloc_offset_i,
  input  logic          alloc_req_i,
  output logic          alloc_gnt_o,

  input  id_t           cnt_id_i,
  output axi_pkg::len_t cnt_len_o,
  output offset_t       cnt_offset_o,
  input  logic          cnt_set_err_i,
  output logic          cnt_err_o,
  input  logic          cnt_len_dec_i,
  input  logic          cnt_offset_inc_i,
  input  logic          cnt_req_i,
  output logic          cnt_gnt_o
);
  localparam int unsigned CntIdxWidth = (MaxTxns > 1) ? $clog2(MaxTxns) : 32'd1;
  typedef logic [CntIdxWidth-1:0]         cnt_idx_t;
  typedef logic [$bits(axi_pkg::len_t):0] cnt_t;
  logic [MaxTxns-1:0]  cnt_len_dec, cnt_offset_inc, cnt_free, cnt_set, err_d, err_q;
  cnt_t                cnt_len_inp;
  cnt_t [MaxTxns-1:0]  cnt_len_oup;
  offset_t                cnt_offset_inp;
  offset_t [MaxTxns-1:0]  cnt_offset_oup;
  cnt_idx_t            cnt_free_idx, cnt_r_idx;
  for (genvar i = 0; i < MaxTxns; i++) begin : gen_cnt
    counter #(
      .WIDTH ( $bits(cnt_t) )
    ) i_cnt_len (
      .clk_i,
      .rst_ni,
      .clear_i    ( 1'b0           ),
      .en_i       ( cnt_len_dec[i] ),
      .load_i     ( cnt_set[i]     ),
      .down_i     ( 1'b1           ),
      .d_i        ( cnt_len_inp    ),
      .q_o        ( cnt_len_oup[i] ),
      .overflow_o (                )  // not used
    );
    counter #(
      .WIDTH ( $bits(offset_t) )
    ) i_cnt_offset (
      .clk_i,
      .rst_ni,
      .clear_i    ( 1'b0              ),
      .en_i       ( cnt_offset_inc[i] ),
      .load_i     ( cnt_set[i]        ),
      .down_i     ( 1'b0              ),
      .d_i        ( cnt_offset_inp    ),
      .q_o        ( cnt_offset_oup[i] ),
      .overflow_o (                   )  // not used
    );
    assign cnt_free[i] = (cnt_len_oup[i] == '0);
  end
  assign cnt_len_inp    = {1'b0, alloc_len_i} + 1;
  assign cnt_offset_inp = alloc_offset_i;

  lzc #(
    .WIDTH  ( MaxTxns ),
    .MODE   ( 1'b0    )  // start counting at index 0
  ) i_lzc (
    .in_i    ( cnt_free     ),
    .cnt_o   ( cnt_free_idx ),
    .empty_o (              )
  );

  logic idq_inp_req, idq_inp_gnt,
        idq_oup_gnt, idq_oup_valid, idq_oup_pop;
  id_queue #(
    .ID_WIDTH ( $bits(id_t) ),
    .CAPACITY ( MaxTxns     ),
    .data_t   ( cnt_idx_t   )
  ) i_idq (
    .clk_i,
    .rst_ni,
    .inp_id_i         ( alloc_id_i    ),
    .inp_data_i       ( cnt_free_idx  ),
    .inp_req_i        ( idq_inp_req   ),
    .inp_gnt_o        ( idq_inp_gnt   ),
    .exists_data_i    ( '0            ),
    .exists_mask_i    ( '0            ),
    .exists_req_i     ( 1'b0          ),
    .exists_o         (/* keep open */),
    .exists_gnt_o     (/* keep open */),
    .oup_id_i         ( cnt_id_i      ),
    .oup_pop_i        ( idq_oup_pop   ),
    .oup_req_i        ( cnt_req_i     ),
    .oup_data_o       ( cnt_r_idx     ),
    .oup_data_valid_o ( idq_oup_valid ),
    .oup_gnt_o        ( idq_oup_gnt   )
  );
  logic [8:0] read_len;
  assign idq_inp_req  = alloc_req_i & alloc_gnt_o;
  assign alloc_gnt_o  = idq_inp_gnt & |(cnt_free);
  assign cnt_gnt_o    = idq_oup_gnt & idq_oup_valid;
  assign read_len     = cnt_len_oup[cnt_r_idx] - 1;
  assign cnt_len_o    = read_len[7:0];
  assign cnt_offset_o = cnt_offset_oup[cnt_r_idx];

  assign idq_oup_pop = cnt_req_i & cnt_gnt_o & cnt_len_dec_i & (cnt_len_o == 8'd0);
  always_comb begin
    cnt_len_dec            = '0;
    cnt_len_dec[cnt_r_idx] = cnt_req_i & cnt_gnt_o & cnt_len_dec_i;
  end
  always_comb begin
    cnt_offset_inc            = '0;
    cnt_offset_inc[cnt_r_idx] = cnt_req_i & cnt_gnt_o & cnt_offset_inc_i;
  end
  always_comb begin
    cnt_set               = '0;
    cnt_set[cnt_free_idx] = alloc_req_i & alloc_gnt_o;
  end
  always_comb begin
    err_d     = err_q;
    cnt_err_o = err_q[cnt_r_idx];
    if (cnt_req_i && cnt_gnt_o && cnt_set_err_i) begin
      err_d[cnt_r_idx] = 1'b1;
      cnt_err_o        = 1'b1;
    end
    if (alloc_req_i && alloc_gnt_o) begin
      err_d[cnt_free_idx] = 1'b0;
    end
  end

  // registers
  `FFARN(err_q, err_d, '0, clk_i, rst_ni)

  `ifndef VERILATOR
  // pragma translate_off
  assume property (@(posedge clk_i) idq_oup_gnt |-> idq_oup_valid)
    else begin $warning("Invalid output at ID queue, read not granted!"); $finish(); end
  // pragma translate_on
  `endif

endmodule
