// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Samuel Riedel  <sriedel@iis.ee.ethz.ch>

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

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

    localparam int unsigned DATA_ADDR_WIDTH = CFG.SET_ALIGN + CFG.COUNT_ALIGN;

    typedef struct packed {
        logic [CFG.FETCH_AW-1:0]     addr;
        logic [CFG.ID_WIDTH_REQ-1:0] id;
    } tag_req_t;

    typedef struct packed {
        logic [CFG.SET_ALIGN-1:0]    set;
        logic                        hit;
        logic                        error;
    } tag_rsp_t;

    typedef struct packed {
        logic [CFG.FETCH_AW-1:0]     addr;
        logic [CFG.ID_WIDTH_REQ-1:0] id;
        logic [CFG.SET_ALIGN-1:0]    set;
        logic                        hit;
        logic                        error;
    } data_req_t;

    typedef logic [CFG.LINE_WIDTH-1:0] data_rsp_t;

    // Multiplex read and write access to the RAMs onto one port, prioritizing
    // write accesses.
    logic [CFG.COUNT_ALIGN:0]   init_count_q;
    logic                       init_phase;

    logic [CFG.COUNT_ALIGN-1:0] tag_addr;
    logic [CFG.SET_COUNT-1:0]   tag_enable;
    logic [CFG.TAG_WIDTH+1:0]   tag_wdata, tag_rdata [CFG.SET_COUNT];
    logic                       tag_write;

    logic [DATA_ADDR_WIDTH-1:0] data_addr;
    logic                       data_enable;
    data_rsp_t                  data_wdata, data_rdata;
    logic                       data_write;

    logic                       req_valid, req_ready;
    tag_req_t                   tag_req_d, tag_req_q;
    tag_rsp_t                   tag_rsp_d, tag_rsp_q;
    logic                       tag_valid, tag_ready;
    logic                       req_handshake, req_ready_ft;
    logic                       tag_handshake;
    logic                       data_handshake;
    logic                       tag_valid_ft, tag_ready_ft;
    logic                       data_valid, data_ready;
    logic                       data_valid_ft, data_ready_ft;
    data_req_t                  data_req_d, data_req_q;
    data_rsp_t                  data_rsp_d, data_rsp_q;

    logic [CFG.SET_ALIGN-1:0] out_set;

    // Initialization and flush FSM
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni)
            init_count_q <= '0;
        else if (flush_valid_i)
            init_count_q <= '0;
        else if (init_count_q != $unsigned(CFG.LINE_COUNT))
            init_count_q <= init_count_q + 1;
    end

    assign init_phase = init_count_q != $unsigned(CFG.LINE_COUNT);
    assign flush_ready_o = flush_valid_i & (init_count_q == $unsigned(CFG.LINE_COUNT));

    // Tag bank port mux
    always_comb begin
        write_ready_o = 0;
        in_ready_o = 0;

        tag_addr   = in_addr_i >> CFG.LINE_ALIGN;
        tag_wdata  = {1'b1, write_error_i, write_tag_i};
        tag_enable = '0;
        tag_write  = 1'b0;
        req_valid  = 1'b0;

        tag_req_d = tag_req_q;

        if (init_phase) begin
            tag_addr   = init_count_q;
            tag_enable = '1;
            tag_write  = 1'b1;
            tag_wdata  = '0;
        end else if (write_valid_i) begin
            tag_addr   = write_addr_i;
            tag_enable = $unsigned(1 << write_set_i);
            tag_write  = 1'b1;
            write_ready_o = 1'b1;
        end else if (in_valid_i) begin
            // Read the tag banks
            tag_enable = '1;
            in_ready_o = req_ready;
            // Store request to data bank
            req_valid       = 1'b1;
            tag_req_d.addr  = in_addr_i;
            tag_req_d.id    = in_id_i;
        end
    end

    // Tag stage
    // Instantiate the RAM sets.
    for (genvar i = 0; i < CFG.SET_COUNT; i++) begin : g_sets
        if (CFG.L1_TAG_SCM) begin : gen_scm
            latch_scm #(
                .ADDR_WIDTH ($clog2(CFG.LINE_COUNT)),
                .DATA_WIDTH (CFG.TAG_WIDTH+2       )
            ) i_tag (
                .clk        ( clk_i                       ),
                .ReadEnable ( tag_enable[i] && !tag_write ),
                .ReadAddr   ( tag_addr                    ),
                .ReadData   ( tag_rdata[i]                ),
                .WriteEnable( tag_enable[i] && tag_write  ),
                .WriteAddr  ( tag_addr                    ),
                .WriteData  ( tag_wdata                   )
            );
        end else begin : gen_sram
            tc_sram #(
                .DataWidth ( CFG.TAG_WIDTH+2 ),
                .NumWords  ( CFG.LINE_COUNT  ),
                .NumPorts  ( 1               )
            ) i_tag (
                .clk_i   ( clk_i         ),
                .rst_ni  ( rst_ni        ),
                .req_i   ( tag_enable[i] ),
                .we_i    ( tag_write     ),
                .addr_i  ( tag_addr      ),
                .wdata_i ( tag_wdata     ),
                .be_i    ( '1            ),
                .rdata_o ( tag_rdata[i]  )
            );
        end
    end

    spill_register #(
        .T (tag_req_t)
    ) i_tag_register (
        .clk_i      (clk_i    ),
        .rst_ni     (rst_ni   ),
        .valid_i    (req_valid),
        .ready_o    (req_ready),
        .data_i     (tag_req_d),
        .valid_o    (tag_valid),
        .ready_i    (tag_ready && !data_write),
        .data_o     (tag_req_q)
    );

    // Determine which RAM line hit, and multiplex that data to the output.
    logic [CFG.TAG_WIDTH-1:0] required_tag;
    logic [CFG.SET_COUNT-1:0] line_hit;

    always_comb begin
        automatic logic [CFG.SET_COUNT-1:0] errors;
        required_tag = tag_req_q.addr >> (CFG.LINE_ALIGN + CFG.COUNT_ALIGN);
        for (int i = 0; i < CFG.SET_COUNT; i++) begin
            line_hit[i] = tag_rdata[i][CFG.TAG_WIDTH+1] && tag_rdata[i][CFG.TAG_WIDTH-1:0] == required_tag;
            errors[i] = tag_rdata[i][CFG.TAG_WIDTH] && line_hit[i];
        end
        tag_rsp_d.hit = |line_hit;
        tag_rsp_d.error = |errors;
    end

    lzc #(.WIDTH(CFG.SET_COUNT)) i_lzc (
        .in_i     ( line_hit      ),
        .cnt_o    ( tag_rsp_d.set ),
        .empty_o  (               )
    );

    `FF(req_handshake, req_valid && req_ready, 1'b0, clk_i, rst_ni)
    `FF(tag_handshake, tag_valid && tag_ready && !data_write, 1'b0, clk_i, rst_ni)
    //`FF(data_handshake, data_valid && data_ready, 1'b0, clk_i, rst_ni)
    assign data_handshake = data_valid && data_ready;

    fall_through_register_2 #(
        .T (tag_rsp_t)
    ) i_tag_ft_register (
        .clk_i        (clk_i     ),
        .rst_ni       (rst_ni    ),
        .clr_i        (1'b0      ),
        .testmode_i   (1'b0      ),
        .valid_i      (req_handshake),
        .ready_o      (req_ready_ft),
        .data_i       (tag_rsp_d   ),
        .valid_o      (tag_valid_ft),
        .ready_i      (tag_valid && tag_ready && !data_write),
        .data_o       (tag_rsp_q   )
    );

    //`ASSERT(req_ftready, req_ready_ft == req_ready)
    //`ASSERT(tag_ftvalid, tag_valid_ft == tag_valid)
    `ASSERT(reqhandshake, req_handshake |-> req_ready_ft);
    `ASSERT(taghandshake, tag_valid && tag_ready && !data_write |->  tag_valid_ft);
    `ASSERT(tagpophandshake, tag_handshake |->  tag_ready_ft);
    `ASSERT(datahandshake, data_handshake |-> data_valid_ft);

    // Data stage
    // Data bank port mux
    always_comb begin
        // Write interface
        data_addr   = '0;
        data_enable = 1'b0;
        data_wdata  = '0;
        data_write  = '0;

        if (!init_phase && write_valid_i) begin
            // Write
            data_addr   = {write_set_i, write_addr_i};
            data_enable = 1'b1;
            data_wdata  = write_data_i;
            data_write  = 1'b1;
        end else if (tag_valid) begin
            data_addr   = {tag_rsp_q.set, tag_req_q.addr[CFG.LINE_ALIGN +: CFG.COUNT_ALIGN]};
            data_enable = 1'b1;
            data_write  = 1'b0;
        end
        // TODO: simplify
    end

    tc_sram #(
        .DataWidth ( CFG.LINE_WIDTH                 ),
        .NumWords  ( CFG.LINE_COUNT * CFG.SET_COUNT ),
        .NumPorts  ( 1                              )
    ) i_data (
        .clk_i   ( clk_i       ),
        .rst_ni  ( rst_ni      ),
        .req_i   ( data_enable ),
        .we_i    ( data_write  ),
        .addr_i  ( data_addr   ),
        .wdata_i ( data_wdata  ),
        .be_i    ( '1          ),
        .rdata_o ( data_rdata  )
    );

    fall_through_register_2 #(
        .T (data_rsp_t)
    ) i_data_ft_register (
        .clk_i        (clk_i     ),
        .rst_ni       (rst_ni    ),
        .clr_i        (1'b0      ),
        .testmode_i   (1'b0      ),
        .valid_i      (tag_handshake),
        .ready_o      (tag_ready_ft),
        .data_i       (data_rdata   ),
        .valid_o      (data_valid_ft),
        .ready_i      (data_handshake),
        .data_o       (data_rsp_q)
    );

    //`ASSERT(tag_ftready, tag_ready_ft == tag_ready)
    //`ASSERT(data_ftvalid, data_valid_ft == data_valid)

    assign data_req_d.addr  = tag_req_q.addr;
    assign data_req_d.id    = tag_req_q.id;
    assign data_req_d.set   = tag_rsp_q.set;
    assign data_req_d.hit   = tag_rsp_q.hit;
    assign data_req_d.error = tag_rsp_q.error;

    spill_register #(
        .T (data_req_t)
    ) i_data_register (
        .clk_i      (clk_i                        ),
        .rst_ni     (rst_ni                       ),
        .valid_i    (tag_valid && !data_write     ),
        .ready_o    (tag_ready                    ),
        .data_i     (data_req_d                   ),
        .valid_o    (data_valid                   ),
        .ready_i    (data_ready                   ),
        .data_o     (data_req_q                   )
    );

    // Generate the remaining output signals.
    assign out_addr_o  = data_req_q.addr;
    assign out_id_o    = data_req_q.id;
    assign out_set_o   = data_req_q.set;
    assign out_hit_o   = data_req_q.hit;
    assign out_data_o  = data_rsp_q;
    assign out_error_o = data_req_q.error;
    assign out_valid_o = data_valid;
    assign data_ready  = out_ready_i;

endmodule

module fall_through_register_2 #(
    parameter type T = logic  // Vivado requires a default value for type parameters.
) (
    input  logic    clk_i,          // Clock
    input  logic    rst_ni,         // Asynchronous active-low reset
    input  logic    clr_i,          // Synchronous clear
    input  logic    testmode_i,     // Test mode to bypass clock gating
    // Input port
    input  logic    valid_i,
    output logic    ready_o,
    input  T        data_i,
    // Output port
    output logic    valid_o,
    input  logic    ready_i,
    output T        data_o
);

  T data_d, data_q;
  logic full_d, full_q;

  always_comb begin
    data_d = data_q;
    data_o = data_q;
    full_d = full_q;
    valid_o = full_q || valid_i;
    ready_o = !full_q || ready_i;

    // Read
    if (ready_i) begin
      full_d = 1'b0;
    end

    // Write
    if (valid_i) begin
      full_d = 1'b1;
      if (!full_q || ready_i) begin
        data_d = data_i;
        data_o = data_i;
      end
    end

    if (valid_i && ready_i) begin
      full_d = full_q;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_q <= '0;
      full_q <= 1'b0;
    end else begin
      data_q <= data_d;
      full_q <= full_d;
    end
  end

endmodule
