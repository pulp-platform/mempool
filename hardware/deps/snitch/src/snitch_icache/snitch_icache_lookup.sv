// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Samuel Riedel  <sriedel@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

/// An actual cache lookup.
module snitch_icache_lookup #(
    parameter snitch_icache_pkg::config_t CFG = '0
)(
    input  logic clk_i,
    input  logic rst_ni,

    input  logic flush_valid_i,
    output logic flush_ready_o,

    input  logic [CFG.FETCH_AW-1:0]     in_addr_i,
    input  logic [CFG.ID_WIDTH_REQ-1:0] in_id_i,
    input  logic                        in_valid_i,
    output logic                        in_ready_o,

    output logic [CFG.FETCH_AW-1:0]     out_addr_o,
    output logic [CFG.ID_WIDTH_REQ-1:0] out_id_o,
    output logic [CFG.SET_ALIGN-1:0]    out_set_o,
    output logic                        out_hit_o,
    output logic [CFG.LINE_WIDTH-1:0]   out_data_o,
    output logic                        out_error_o,
    output logic                        out_valid_o,
    input  logic                        out_ready_i,

    input  logic [CFG.COUNT_ALIGN-1:0]  write_addr_i,
    input  logic [CFG.SET_ALIGN-1:0]    write_set_i,
    input  logic [CFG.LINE_WIDTH-1:0]   write_data_i,
    input  logic [CFG.TAG_WIDTH-1:0]    write_tag_i,
    input  logic                        write_error_i,
    input  logic                        write_valid_i,
    output logic                        write_ready_o
);
    logic valid_and_hit;
    assign valid_and_hit = out_valid_o & out_hit_o;

    `ifndef SYNTHESIS
    initial assert(CFG != '0);
    `endif

    localparam int unsigned DataAddrWdith = CFG.SET_ALIGN + CFG.COUNT_ALIGN;

    typedef struct packed {
        logic [CFG.FETCH_AW-1:0]     addr;
        logic [CFG.COUNT_ALIGN-1:0]  cset;
        logic [CFG.LINE_WIDTH-1:0]   data;
        logic [CFG.ID_WIDTH_REQ-1:0] id;
        logic                        write;
    } req_t;

    // Multiplex read and write access to the RAMs onto one port, prioritizing
    // write accesses.
    logic [CFG.COUNT_ALIGN-1:0] ram_addr                             ;
    logic [CFG.SET_COUNT-1:0]   ram_enable                           ;
    logic [CFG.LINE_WIDTH-1:0]  ram_wdata, ram_rdata;
    logic [CFG.TAG_WIDTH+1:0]   ram_wtag,  ram_rtag  [CFG.SET_COUNT] ;
    logic                       ram_write                            ;
    logic                       ram_write_q;
    logic [CFG.COUNT_ALIGN:0]   init_count_q;
    logic [CFG.COUNT_ALIGN-1:0] data_addr;
    logic [DataAddrWdith-1:0]   data_bank_addr;
    req_t                       data_req_d, data_req_q;
    logic                       req_valid, req_ready;

    logic out_hit, out_error;
    logic [CFG.SET_ALIGN-1:0] out_set;

    always_comb begin : p_portmux
        write_ready_o = 0;
        in_ready_o = 0;

        ram_addr   = in_addr_i >> CFG.LINE_ALIGN;
        ram_wdata  = write_data_i;
        ram_wtag   = {1'b1, write_error_i, write_tag_i};
        ram_enable = '0;
        ram_write  = 1'b0;
        req_valid  = 1'b0;

        data_req_d = data_req_q;

        if (init_count_q != $unsigned(CFG.LINE_COUNT)) begin
            ram_addr   = init_count_q;
            ram_enable = '1;
            ram_write  = 1'b1;
            ram_wdata  = '0;
            ram_wtag   = '0;
        end else  if (write_valid_i) begin
            ram_addr   = write_addr_i;
            ram_enable = $unsigned(1 << write_set_i);
            ram_write  = 1'b1;
            write_ready_o = 1'b1; // From Fall-through register
            // Store request to data bank
            req_valid        = 1'b1;
            data_req_d.addr  = write_addr_i;
            data_req_d.cset  = write_set_i;
            data_req_d.data  = write_data_i;
            data_req_d.write = 1'b1;
        end else if (in_valid_i) begin
            // Read the tag banks
            ram_enable = '1;
            in_ready_o = out_ready_i;
            // Store request to data bank
            req_valid        = 1'b1;
            data_req_d.addr  = in_addr_i;
            data_req_d.id    = in_id_i;
            data_req_d.write = 1'b0;
        end
    end

    assign flush_ready_o = flush_valid_i & (init_count_q == $unsigned(CFG.LINE_COUNT));

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni)
            init_count_q <= '0;
        else if (flush_valid_i)
            init_count_q <= '0;
        else if (init_count_q != $unsigned(CFG.LINE_COUNT))
            init_count_q <= init_count_q + 1;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            ram_write_q <= 0;
        end else begin
            ram_write_q <= ram_write;
        end
    end

    // The address register keeps track of additional metadata alongside the
    // looked up tag and data.
    logic valid_q, valid_d;
    logic [CFG.FETCH_AW-1:0] addr_q;
    logic [CFG.ID_WIDTH_REQ-1:0] id_q;

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni) begin
            addr_q <= '0;
            id_q   <= '0;
        end else if (valid_d && out_ready_i) begin
            addr_q <= data_req_q.addr;
            id_q   <= data_req_q.id;
        end
    end

    `FFLARN(out_hit_o, out_hit, valid_d & out_ready_i, 1'b0, clk_i, rst_ni)
    `FFLARN(out_error_o, out_error, valid_d & out_ready_i, 1'b0, clk_i, rst_ni)
    `FFLARN(out_set_o, out_set, valid_d & out_ready_i, '0, clk_i, rst_ni)

    // Store data while reading the tag
    `FFLARN(data_req_q, data_req_d, req_valid & out_ready_i, '0, clk_i, rst_ni)
    `FF(valid_d, req_valid, 1'b0)

    `FF(valid_q, valid_d & ~data_req_q.write, 1'b0)

    // Instantiate the RAM sets.
    for (genvar i = 0; i < CFG.SET_COUNT; i++) begin : g_sets
        if (CFG.L1_TAG_SCM) begin : gen_scm
            latch_scm #(
                .ADDR_WIDTH ($clog2(CFG.LINE_COUNT)),
                .DATA_WIDTH (CFG.TAG_WIDTH+2       )
            ) i_tag (
                .clk        (clk_i                      ),
                .ReadEnable (ram_enable[i] && !ram_write),
                .ReadAddr   (ram_addr                   ),
                .ReadData   (ram_rtag[i]                ),
                .WriteEnable(ram_enable[i] && ram_write ),
                .WriteAddr  (ram_addr                   ),
                .WriteData  (ram_wtag                   )
            );
        end else begin : gen_sram
            tc_sram #(
                .DataWidth ( CFG.TAG_WIDTH+2 ),
                .NumWords  ( CFG.LINE_COUNT  ),
                .NumPorts  ( 1               )
            ) i_tag (
                .clk_i   ( clk_i         ),
                .rst_ni  ( rst_ni        ),
                .req_i   ( ram_enable[i] ),
                .we_i    ( ram_write     ),
                .addr_i  ( ram_addr      ),
                .wdata_i ( ram_wtag      ),
                .be_i    ( '1            ),
                .rdata_o ( ram_rtag[i]   )
            );
        end
    end

    // Single data bank for all sets
    assign data_addr = {data_req_q.write ? data_req_q.addr : data_req_q.addr >> CFG.LINE_ALIGN};
    assign data_bank_addr = {data_req_q.write ? data_req_q.cset : out_set, data_addr};
    tc_sram #(
        .DataWidth ( CFG.LINE_WIDTH                 ),
        .NumWords  ( CFG.LINE_COUNT * CFG.SET_COUNT ),
        .NumPorts  ( 1                              )
    ) i_data (
        .clk_i   ( clk_i            ),
        .rst_ni  ( rst_ni           ),
        .req_i   ( valid_d          ),
        .we_i    ( data_req_q.write ),
        .addr_i  ( data_bank_addr   ),
        .wdata_i ( data_req_q.data  ),
        .be_i    ( '1               ),
        .rdata_o ( ram_rdata        )
    );

    // Determine which RAM line hit, and multiplex that data to the output.
    logic [CFG.TAG_WIDTH-1:0] required_tag;
    logic [CFG.SET_COUNT-1:0] line_hit;

    always_comb begin
        automatic logic [CFG.SET_COUNT-1:0] errors;
        required_tag = data_req_q.addr >> (CFG.LINE_ALIGN + CFG.COUNT_ALIGN);
        for (int i = 0; i < CFG.SET_COUNT; i++) begin
            line_hit[i] = ram_rtag[i][CFG.TAG_WIDTH+1] && ram_rtag[i][CFG.TAG_WIDTH-1:0] == required_tag;
            errors[i] = ram_rtag[i][CFG.TAG_WIDTH] && line_hit[i];
        end
        out_hit = |line_hit & ~ram_write_q; // Don't let refills trigger "valid" lookups
        out_error = |errors;
    end

    assign out_data_o = out_hit_o ? ram_rdata : '0;

    lzc #(.WIDTH(CFG.SET_COUNT)) i_lzc (
        .in_i     ( line_hit  ),
        .cnt_o    ( out_set   ),
        .empty_o  (           )
    );

    // Generate the remaining output signals.
    assign out_addr_o  = addr_q;
    assign out_id_o    = id_q;
    assign out_valid_o = valid_q;

endmodule
