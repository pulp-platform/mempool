// Copyright (c) 2017-2018 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// A simple prefetcher private to each port.
///
/// The outgoing request/response interface is a bit quirky in that the requests
/// have a binary ID of length N, while the responses have a bitmask ID of
/// length 2**N. This ensures that the cache can serve multiple responses at a
/// time, if possible.
module snitch_icache_prefetch #(
    parameter snitch_icache_pkg::config_t CFG = '0,
    parameter int unsigned             PREFETCH_ID = 0
)(
    input  logic  clk_i,
    input  logic  rst_ni,

    input  logic [CFG.FETCH_AW-1:0]   in_addr_i,
    input  logic                      in_valid_i,
    output logic [CFG.LINE_WIDTH-1:0] in_data_o,
    output logic                      in_ready_o,
    output logic                      in_error_o,

    output logic [CFG.FETCH_AW-1:0]      out_req_addr_o,
    output logic [CFG.ID_WIDTH_REQ-1:0]  out_req_id_o,
    output logic                         out_req_valid_o,
    input  logic                         out_req_ready_i,

    input  logic [CFG.LINE_WIDTH-1:0]    out_rsp_data_i,
    input  logic                         out_rsp_error_i,
    input  logic [CFG.ID_WIDTH_RESP-1:0] out_rsp_id_i,
    input  logic                         out_rsp_valid_i,
    output logic                         out_rsp_ready_o
);

    `ifndef SYNTHESIS
    initial assert(CFG != '0);
    `endif

    // The request signals that lead into the selector.
    typedef struct packed {
        logic [CFG.FETCH_AW-1:0] addr;
        logic valid;
        logic ready;
    } request_t;
    request_t req_main, req_side;

    // Generate a register that keeps track if an outgoing request has been
    // generated for a new incoming request. Once the outgoing request is sent,
    // the `served` register goes high. The register is cleared once a
    // response is sent to the incoming request as indicated by `in_ready`.
    logic served_q;

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni)
            served_q <= 1'b0;
        else
            served_q <= in_valid_i & ~in_ready_o & (served_q | req_main.ready);
    end

    always_comb begin
        req_main.addr = in_addr_i;
        req_main.valid = in_valid_i & ~served_q;
    end

    // Generate additional registers which hold prefetch requests.
    logic update_prefetch;
    logic prefetch_pending, prefetch_pending_set, prefetch_pending_clr;
    logic req_side_valid_q;

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni)
            req_side_valid_q <= 1'b0;
        else if (update_prefetch)
            req_side_valid_q <= req_main.valid;
    end
    assign req_side.valid = req_side_valid_q & ~prefetch_pending;

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni)
            req_side.addr <= '0;
        else if (update_prefetch && req_main.valid)
            req_side.addr <= req_main.addr + $unsigned(1 << CFG.LINE_ALIGN);
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni)
            prefetch_pending <= 1'b0;
        else if (prefetch_pending_set || prefetch_pending_clr)
            prefetch_pending <= prefetch_pending_set && ~prefetch_pending_clr;
    end

    assign update_prefetch = (req_main.valid && !req_side_valid_q) || (req_side_valid_q && req_side.ready);

    // The request selector decides whether to forward the incoming request or
    // mix in a prefetch request. The former takes priority over the latter, but
    // once a request is started, the selector stays committed until completion.
    struct packed {
        logic committed; // whether the selector is committed to a request
        logic selected; // which request the selector is committed to
    } state_sd, state_sq;
    logic request_sel; // selector for the request multiplexer

    always_ff @(posedge clk_i, negedge rst_ni) begin : ps_state
        if (!rst_ni) begin
            state_sq <= '{default: 0};
        end else begin
            state_sq <= state_sd;
        end
    end

    always_comb begin : pc_committer
        state_sd = state_sq;

        // Commit if we have pending requests.
        if (!state_sq.committed || out_req_ready_i) begin
            if (req_main.valid) begin
                state_sd.committed = !out_req_ready_i;
                state_sd.selected = 1'b0;
            end else if (req_side.valid) begin
                state_sd.committed = !out_req_ready_i;
                state_sd.selected = 1'b1;
            end else begin
                state_sd.committed = 1'b0;
                state_sd.selected = 1'b0;
            end
        end

        // Switch the muxer based on the committed request, or the newly picked
        // request.
        request_sel = state_sq.committed ? state_sq.selected : state_sd.selected;
    end

    // Route the appropriate signals to the output based on the selection.
    always_comb begin : pc_reqmux
        req_main.ready = 1'b0;
        req_side.ready = 1'b0;

        out_req_valid_o = state_sq.committed ?
                         (state_sq.selected  ? req_side.valid : req_main.valid)
                                             : (req_side.valid | req_main.valid);
        unique case (request_sel)
            0: begin
                out_req_addr_o = req_main.addr;
                out_req_id_o = {PREFETCH_ID[CFG.ID_WIDTH_REQ-2:0], 1'b0};
                req_main.ready = out_req_ready_i;
            end
            1: begin
                out_req_addr_o = req_side.addr;
                out_req_id_o = {PREFETCH_ID[CFG.ID_WIDTH_REQ-2:0], 1'b1};
                req_side.ready = out_req_ready_i;
            end
            default: begin
                out_req_addr_o = '0;
                out_req_valid_o = 1'b0;
                out_req_id_o = {PREFETCH_ID[CFG.ID_WIDTH_REQ-2:0], 1'b0};
            end
        endcase
    end

    // Pass through the responses.
    assign in_data_o = out_rsp_data_i;
    assign in_error_o = out_rsp_error_i;
    assign in_ready_o = out_rsp_valid_i && out_rsp_id_i[2*PREFETCH_ID];
    assign out_rsp_ready_o = 1'b1;
    assign prefetch_pending_set = out_req_valid_o & out_req_ready_i & (out_req_id_o[0] == 1);
    assign prefetch_pending_clr = out_rsp_valid_i & out_rsp_id_i[2*PREFETCH_ID+1];

endmodule
