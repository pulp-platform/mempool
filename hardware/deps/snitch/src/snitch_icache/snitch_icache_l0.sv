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
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

/// A simple single-line cache private to each port.
module snitch_icache_l0 #(
    parameter snitch_icache_pkg::config_t CFG = '0,
    parameter int unsigned PREFETCH_ID = 0
)(
    input  logic clk_i,
    input  logic rst_ni,

    input  logic [CFG.FETCH_AW-1:0]   in_addr_i,
    input  logic                      in_valid_i,
    output logic [CFG.FETCH_DW-1:0]   in_data_o,
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

    typedef struct packed {
        logic [CFG.L0_TAG_WIDTH-1:0] tag;
        logic                     vld;
    } tag_t;

    logic [CFG.L0_TAG_WIDTH-1:0] addr_tag, addr_tag_prefetch;

    tag_t [CFG.L0_TAG_WIDTH-1:0] tag;
    logic [CFG.LINE_WIDTH-1:0][CFG.LINE_WIDTH-1:0] data;

    logic [CFG.L0_LINE_COUNT-1:0] hit, hit_prefetch;
    logic hit_any;
    logic miss;

    logic [CFG.L0_LINE_COUNT-1:0] evict_strb;
    logic [CFG.L0_LINE_COUNT-1:0] validate_strb;

    // Holds the onehot signal for the line being refilled at the moment
    logic [CFG.L0_LINE_COUNT-1:0] pending_line_refill_q;
    logic pending_refill_q, pending_refill_d;

    logic evict_req;
    logic last_cycle_was_miss_q;

    `FF(last_cycle_was_miss_q, miss, '0)

    assign evict_req = miss & ~last_cycle_was_miss_q;

    assign addr_tag = in_addr_i >> CFG.LINE_ALIGN;

    always_comb begin : tag_cmp_fetch
        hit = '0;
        for (int i = 0; i < CFG.L0_LINE_COUNT; i++) begin
            if (tag[i].vld && tag[i].tag == addr_tag) begin
                hit[i] = 1'b1;
            end
        end
    end

    always_comb begin : tag_cmp_prefetcher
        hit_prefetch = '0;
        for (int i = 0; i < CFG.L0_LINE_COUNT; i++) begin
            if (tag[i].vld && tag[i].tag == addr_tag_prefetch) begin
                hit_prefetch[i] = 1'b1;
            end
        end
    end

    assign hit_any = |hit;
    assign miss = ~hit_any & in_valid_i;

    for (genvar i = 0; i < CFG.L0_LINE_COUNT; i++) begin : gen_array
        // Tag Array
        always_ff @(posedge clk_i or negedge rst_ni) begin
            if (!rst_ni) begin
                tag[i].vld <= 0;
                tag[i].tag <= 0;
            end else begin
                if (evict_strb[i]) begin
                    tag[i].vld <= 1'b0;
                    tag[i].tag <= addr_tag;
                end else if (validate_strb[i]) begin
                    tag[i].vld <= 1'b1;
                end
            end
        end
        if (CFG.EARLY_LATCH) begin : gen_latch
            // Data Array
            always_latch begin
                if (clk_i && validate_strb[i]) begin
                    data[i] <= out_rsp_data_i;
                end
            end
        end else begin : gen_ff
            `FFLNR(data[i], out_rsp_data_i, validate_strb[i], clk_i)
        end
    end

    //
    // HIT
    //
    assign in_ready_o = hit_any;

    logic [CFG.LINE_WIDTH-1:0] select_line_data;
    always_comb begin : data_muxer
        select_line_data = '0;
        for (int unsigned i = 0; i < CFG.L0_LINE_COUNT; i++) begin
            select_line_data |= (hit[i] ? data[i] : '0);
        end
        if (CFG.LINE_ALIGN == CFG.FETCH_ALIGN)
          in_data_o = select_line_data >> (in_addr_i[CFG.LINE_ALIGN] * CFG.FETCH_DW);
        else
          in_data_o = select_line_data >> (in_addr_i[CFG.LINE_ALIGN-1:CFG.FETCH_ALIGN] * CFG.FETCH_DW);
    end

    //
    // Evictor
    //
    localparam BUGU = CFG.L0_LINE_COUNT;
    logic [$clog2(BUGU)-1:0] cnt_d, cnt_q;

    always_comb begin : evictor
        evict_strb = '0;
        cnt_d = cnt_q;

        if (evict_req) begin
            evict_strb = 1 << cnt_q;
            cnt_d = cnt_q + 1;
        end
    end

    `FF(cnt_q, cnt_d, '0)

    //
    // Miss Handling
    //
    typedef struct packed {
        logic                    is_prefetch;
        logic [CFG.FETCH_AW-1:0] addr;
    } req_t;

    req_t refill, prefetch;
    logic refill_valid, prefetch_valid;
    logic refill_ready, prefetch_ready;

    assign refill.addr = addr_tag << CFG.LINE_ALIGN;
    assign refill.is_prefetch = 1'b0;
    assign refill_valid = ~pending_refill_q & miss;

    `FFLNR(pending_line_refill_q, evict_strb, evict_req, clk_i)
    `FF(pending_refill_q, pending_refill_d, '0);

    always_comb begin
        pending_refill_d = pending_refill_q;
        // re-set condition
        if (pending_refill_q) begin
            if (out_rsp_valid_i & out_rsp_ready_o) begin
                pending_refill_d = 1'b0;
            end
        // set condition
        end else begin
            if (refill_valid & refill_ready) begin
                pending_refill_d = 1'b1;
            end
        end
    end

    assign validate_strb = out_rsp_valid_i ? pending_line_refill_q : '0;
    assign out_rsp_ready_o = 1'b1;

    assign in_error_o = '0;

    req_t out_req;

    assign out_req_addr_o = out_req.addr;
    assign out_req_id_o = {PREFETCH_ID, out_req.is_prefetch};

    stream_arbiter #(
        .DATA_T (req_t),
        .N_INP  ( 2 ),
        .ARBITER ("rr") // TODO(zarubaf): Set to "prio"
    ) i_stream_arbiter (
        .clk_i,
        .rst_ni,
        .inp_data_i({prefetch, refill}),
        .inp_valid_i({prefetch_valid, refill_valid}),
        .inp_ready_o({prefetch_ready, refill_ready}),
        .oup_data_o(out_req),
        .oup_valid_o(out_req_valid_o),
        .oup_ready_i(out_req_ready_i)
    );

    typedef struct packed {
        logic vld;
        logic [CFG.FETCH_AW-1:0] addr;
    } prefetch_req_t;

    prefetch_req_t prefetch_req_q, prefetch_req_d, prefetcher_out;

    // TODO(zarubaf): Add (linear) prefetching
    assign prefetcher_out = '0;
    // assign prefetcher_out.vld = out_rsp_valid_i & out_rsp_ready_o & ~out_rsp_id_i[0] & ~hit_prefetch;
    // assign prefetcher_out.addr = (1 + addr_tag) << CFG.LINE_ALIGN;

    // check whether cache-line we want to pre-fetch is already present
    assign addr_tag_prefetch = prefetcher_out.addr >> CFG.LINE_ALIGN;

    always_comb begin
        prefetch_req_d = prefetch_req_q;

        if (prefetch_ready) prefetch_req_d.vld = 1'b0;

        if (prefetcher_out.vld && !prefetch_req_d.vld) begin
            prefetch_req_d.vld = 1'b1;
            prefetch_req_d.addr = prefetcher_out.addr;
        end
    end

    assign prefetch.is_prefetch = 1'b1;
    assign prefetch.addr = prefetch_req_q.addr;
    assign prefetch_valid = prefetch_req_q.vld;

    `FF(prefetch_req_q.vld, prefetch_req_d.vld, '0)
    `FFNR(prefetch_req_q.addr, prefetch_req_d.addr, clk_i)

endmodule
