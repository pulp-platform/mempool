// Copyright (c) 2017-2019 ETH Zurich, University of Bologna
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

module snitch_icache #(
    /// Number of request (fetch) ports
    parameter int NR_FETCH_PORTS = -1,
    /// L0 Cache Line Count
    parameter int L0_LINE_COUNT = -1,
    /// Cache Line Width
    parameter int LINE_WIDTH = -1,
    /// The number of cache lines per set. Power of two; >= 2.
    parameter int LINE_COUNT = -1,
    /// The set associativity of the cache. Power of two; >= 1.
    parameter int SET_COUNT = 1,
    /// Fetch interface address width. Power of two; >= 1.
    parameter int FETCH_AW = -1,
    /// Fetch interface data width. Power of two; >= 8.
    parameter int FETCH_DW = -1,
    /// Fill interface address width. Power of two; >= 1.
    parameter int FILL_AW = -1,
    /// Fill interface data width. Power of two; >= 8.
    parameter int FILL_DW = -1,
    /// Add an optional private cache for each port. If enabled, the early
    /// cache will be added if the fetch data width is smaller than the cache
    /// line.
    parameter bit EARLY_ENABLED = 1,
    /// This reduces area impact at the cost of
    /// increased hassle of having latches in
    /// the design.
    /// i_snitch_icache/gen_prefetcher*i_snitch_icache_l0/data*/Q
    parameter bit EARLY_LATCH = 0,
    /// Make the early cache serve responses combinatorially if possible. Set
    /// this to 0 to cut combinatorial paths into the fetch interface.
    parameter bit EARLY_FALLTHROUGH = 0
)(
    input  logic clk_i,
    input  logic rst_ni,

    input  logic [NR_FETCH_PORTS-1:0][FETCH_AW-1:0] inst_addr_i,
    output logic [NR_FETCH_PORTS-1:0][FETCH_DW-1:0] inst_data_o,
    input  logic [NR_FETCH_PORTS-1:0]               inst_valid_i,
    output logic [NR_FETCH_PORTS-1:0]               inst_ready_o,
    output logic [NR_FETCH_PORTS-1:0]               inst_error_o,
    // AXI-like read-only interface
    output logic [FILL_AW-1:0]   refill_qaddr_o,
    output logic [7:0]           refill_qlen_o,
    output logic                 refill_qvalid_o,
    input  logic                 refill_qready_i,

    input  logic [FILL_DW-1:0]   refill_pdata_i,
    input  logic                 refill_perror_i,
    input  logic                 refill_pvalid_i,
    input  logic                 refill_plast_i,
    output logic                 refill_pready_o
);

    // Bundle the parameters up into a proper configuration struct that we can
    // pass to submodules.
    localparam snitch_icache_pkg::config_t CFG = '{
        NR_FETCH_PORTS:    NR_FETCH_PORTS,
        LINE_WIDTH:        LINE_WIDTH,
        LINE_COUNT:        LINE_COUNT,
        L0_LINE_COUNT:     L0_LINE_COUNT,
        SET_COUNT:         SET_COUNT,
        PENDING_COUNT:     2,
        FETCH_AW:          FETCH_AW,
        FETCH_DW:          FETCH_DW,
        FILL_AW:           FILL_AW,
        FILL_DW:           FILL_DW,
        EARLY_ENABLED:     EARLY_ENABLED,
        EARLY_LATCH:       EARLY_LATCH,
        EARLY_FALLTHROUGH: EARLY_FALLTHROUGH,

        FETCH_ALIGN: $clog2(FETCH_DW/8),
        FILL_ALIGN:  $clog2(FILL_DW/8),
        LINE_ALIGN:  $clog2(LINE_WIDTH/8),
        COUNT_ALIGN: $clog2(LINE_COUNT),
        SET_ALIGN:   $clog2(SET_COUNT),
        TAG_WIDTH:   FETCH_AW - $clog2(LINE_WIDTH/8) - $clog2(LINE_COUNT) + 1,
        L0_TAG_WIDTH: FETCH_AW - $clog2(LINE_WIDTH/8),
        ID_WIDTH_REQ: $clog2(NR_FETCH_PORTS) + 1,
        ID_WIDTH_RESP: 2*NR_FETCH_PORTS,
        PENDING_IW:  $clog2(2)
    };

    // pragma translate_off
    `ifndef VERILATOR
    // Check invariants.
    initial begin
        assert(L0_LINE_COUNT > 0);
        assert(LINE_WIDTH > 0);
        assert(LINE_COUNT > 1);
        assert(SET_COUNT > 0);
        assert(FETCH_AW > 0);
        assert(FETCH_DW > 0);
        assert(FILL_AW > 0);
        assert(FILL_DW > 0);
        assert(2**$clog2(LINE_WIDTH) == LINE_WIDTH);
        assert(2**$clog2(LINE_COUNT) == LINE_COUNT);
        assert(2**$clog2(SET_COUNT) == SET_COUNT);
        assert(2**$clog2(FETCH_AW) == FETCH_AW);
        assert(2**$clog2(FETCH_DW) == FETCH_DW);
        assert(2**$clog2(FILL_AW) == FILL_AW);
        assert(2**$clog2(FILL_DW) == FILL_DW);
    end
    `endif
    // pragma translate_on

    // Instantiate the optional early cache, or bypass it.
    logic [NR_FETCH_PORTS-1:0][FETCH_AW-1:0]   early_addr;
    logic [NR_FETCH_PORTS-1:0][LINE_WIDTH-1:0] early_data;
    logic [NR_FETCH_PORTS-1:0]                 early_valid;
    logic [NR_FETCH_PORTS-1:0]                 early_ready;
    logic [NR_FETCH_PORTS-1:0]                 early_error;

    // The prefetch module is responsible for taking the 1-channel valid/ready
    // transaction from the early cache and translate it into a 2-channel
    // transaction. Once the actual incoming request has been accepted on the
    // `req` channel, the prefetcher issues another low-priority request for the
    // next cache line.
    typedef struct packed {
        logic [CFG.FETCH_AW-1:0]     addr;
        logic [CFG.ID_WIDTH_REQ-1:0] id;
    } prefetch_req_t;

    typedef struct packed {
        logic [CFG.LINE_WIDTH-1:0]    data;
        logic                         error;
        logic [CFG.ID_WIDTH_RESP-1:0] id;
    } prefetch_resp_t;

    prefetch_req_t [NR_FETCH_PORTS-1:0] prefetch_req       ;
    logic          [NR_FETCH_PORTS-1:0] prefetch_req_valid ;
    logic          [NR_FETCH_PORTS-1:0] prefetch_req_ready ;

    prefetch_req_t prefetch_lookup_req       ;
    logic          prefetch_lookup_req_valid ;
    logic          prefetch_lookup_req_ready ;

    prefetch_resp_t [NR_FETCH_PORTS-1:0]  prefetch_rsp       ;
    logic           [NR_FETCH_PORTS-1:0]  prefetch_rsp_valid ;
    logic           [NR_FETCH_PORTS-1:0]  prefetch_rsp_ready ;

    prefetch_resp_t prefetch_lookup_rsp       ;
    logic           prefetch_lookup_rsp_valid ;
    logic           prefetch_lookup_rsp_ready ;

    for (genvar i = 0; i < NR_FETCH_PORTS; i++) begin : gen_prefetcher
        snitch_icache_l0 #(
            .CFG         ( CFG ),
            .PREFETCH_ID ( i   )
        ) i_snitch_icache_l0 (
            .clk_i,
            .rst_ni,

            .in_addr_i       ( inst_addr_i  [i]       ),
            .in_valid_i      ( inst_valid_i [i]       ),
            .in_data_o       ( inst_data_o  [i]       ),
            .in_ready_o      ( inst_ready_o [i]       ),
            .in_error_o      ( inst_error_o [i]       ),

            .out_req_addr_o  ( prefetch_req[i].addr   ),
            .out_req_id_o    ( prefetch_req[i].id     ),
            .out_req_valid_o ( prefetch_req_valid [i] ),
            .out_req_ready_i ( prefetch_req_ready [i] ),

            .out_rsp_data_i  ( prefetch_rsp[i].data   ),
            .out_rsp_error_i ( prefetch_rsp[i].error  ),
            .out_rsp_id_i    ( prefetch_rsp[i].id     ),
            .out_rsp_valid_i ( prefetch_rsp_valid [i] ),
            .out_rsp_ready_o ( prefetch_rsp_ready [i] )
        );
    end

    /// Arbitrate cache port

    // 1. Request Side
    stream_arbiter #(
        .DATA_T ( prefetch_req_t ),
        .N_INP  ( NR_FETCH_PORTS )
    ) i_stream_arbiter (
        .clk_i,
        .rst_ni,
        .inp_data_i  ( prefetch_req              ),
        .inp_valid_i ( prefetch_req_valid        ),
        .inp_ready_o ( prefetch_req_ready        ),
        .oup_data_o  ( prefetch_lookup_req       ),
        .oup_valid_o ( prefetch_lookup_req_valid ),
        .oup_ready_i ( prefetch_lookup_req_ready )
    );

    // 2. Response Side
    // This breaks if the pre-fetcher would not alway be ready
    // which is the case for the moment
    for (genvar i = 0; i < NR_FETCH_PORTS; i++) begin
        assign prefetch_rsp[i] = prefetch_lookup_rsp;
        // check if one of the ID bits is set
        assign prefetch_rsp_valid[i] = ((|((prefetch_rsp[i].id >> 2*i) & 2'b11)) & prefetch_lookup_rsp_valid);
    end
    assign prefetch_lookup_rsp_ready = |prefetch_rsp_ready;

    /// Tag lookup

    // The lookup module contains the actual cache RAMs and performs lookups.
    logic [CFG.FETCH_AW-1:0]     lookup_addr  ;
    logic [CFG.ID_WIDTH_REQ-1:0] lookup_id    ;
    logic [CFG.SET_ALIGN-1:0]    lookup_set   ;
    logic                        lookup_hit   ;
    logic [CFG.LINE_WIDTH-1:0]   lookup_data  ;
    logic                        lookup_error ;
    logic                        lookup_valid ;
    logic                        lookup_ready ;

    logic [CFG.COUNT_ALIGN-1:0]  write_addr  ;
    logic [CFG.SET_ALIGN-1:0]    write_set   ;
    logic [CFG.LINE_WIDTH-1:0]   write_data  ;
    logic [CFG.TAG_WIDTH-1:0]    write_tag   ;
    logic                        write_error ;
    logic                        write_valid ;
    logic                        write_ready ;

    snitch_icache_lookup #(CFG) i_lookup (
        .clk_i,
        .rst_ni,

        .in_addr_i     ( prefetch_lookup_req.addr  ),
        .in_id_i       ( prefetch_lookup_req.id    ),
        .in_valid_i    ( prefetch_lookup_req_valid ),
        .in_ready_o    ( prefetch_lookup_req_ready ),

        .out_addr_o    ( lookup_addr        ),
        .out_id_o      ( lookup_id          ),
        .out_set_o     ( lookup_set         ),
        .out_hit_o     ( lookup_hit         ),
        .out_data_o    ( lookup_data        ),
        .out_error_o   ( lookup_error       ),
        .out_valid_o   ( lookup_valid       ),
        .out_ready_i   ( lookup_ready       ),

        .write_addr_i  ( write_addr         ),
        .write_set_i   ( write_set          ),
        .write_data_i  ( write_data         ),
        .write_tag_i   ( write_tag          ),
        .write_error_i ( write_error        ),
        .write_valid_i ( write_valid        ),
        .write_ready_o ( write_ready        )
    );

    // The miss handler module deals with the result of the lookup. It also
    // keeps track of the pending refills and ensures that no redundant memory
    // requests are made. Upon refill completion, it sends a new tag/data item
    // to the lookup module and the received data to the prefetch module.
    logic [CFG.FETCH_AW-1:0]     refill_req_addr  ;
    logic [CFG.PENDING_IW-1:0]   refill_req_id    ;
    logic                        refill_req_valid ;
    logic                        refill_req_ready ;

    logic [CFG.LINE_WIDTH-1:0]   refill_rsp_data  ;
    logic                        refill_rsp_error ;
    logic [CFG.PENDING_IW-1:0]   refill_rsp_id    ;
    logic                        refill_rsp_valid ;
    logic                        refill_rsp_ready ;

    snitch_icache_handler #(CFG) i_handler (
        .clk_i,
        .rst_ni,

        .in_req_addr_i   ( lookup_addr        ),
        .in_req_id_i     ( lookup_id          ),
        .in_req_set_i    ( lookup_set         ),
        .in_req_hit_i    ( lookup_hit         ),
        .in_req_data_i   ( lookup_data        ),
        .in_req_error_i  ( lookup_error       ),
        .in_req_valid_i  ( lookup_valid       ),
        .in_req_ready_o  ( lookup_ready       ),

        .in_rsp_data_o   ( prefetch_lookup_rsp.data  ),
        .in_rsp_error_o  ( prefetch_lookup_rsp.error ),
        .in_rsp_id_o     ( prefetch_lookup_rsp.id    ),
        .in_rsp_valid_o  ( prefetch_lookup_rsp_valid ),
        .in_rsp_ready_i  ( prefetch_lookup_rsp_ready ),

        .write_addr_o    ( write_addr         ),
        .write_set_o     ( write_set          ),
        .write_data_o    ( write_data         ),
        .write_tag_o     ( write_tag          ),
        .write_error_o   ( write_error        ),
        .write_valid_o   ( write_valid        ),
        .write_ready_i   ( write_ready        ),

        .out_req_addr_o  ( refill_req_addr    ),
        .out_req_id_o    ( refill_req_id      ),
        .out_req_valid_o ( refill_req_valid   ),
        .out_req_ready_i ( refill_req_ready   ),

        .out_rsp_data_i  ( refill_rsp_data    ),
        .out_rsp_error_i ( refill_rsp_error   ),
        .out_rsp_id_i    ( refill_rsp_id      ),
        .out_rsp_valid_i ( refill_rsp_valid   ),
        .out_rsp_ready_o ( refill_rsp_ready   )
    );

    // AXI-like read-only interface
    typedef struct packed {
        logic [FILL_AW-1:0] addr;
        logic [7:0]         len;
    } refill_req_t;

    typedef struct packed {
        logic [FILL_DW-1:0] data;
        logic               error;
        logic               last;
    } refill_resp_t;

    refill_req_t          refill_req, refill_req_q;
    logic                 refill_qvalid;
    logic                 refill_qready;

    refill_resp_t         refill_resp, refill_resp_q;
    logic                 refill_pvalid_q;
    logic                 refill_pready_q;

    // Instantiate the cache refill module which emits AXI transactions.
    snitch_icache_refill #(CFG) i_refill (
        .clk_i,
        .rst_ni,

        .in_req_addr_i  ( refill_req_addr  ),
        .in_req_id_i    ( refill_req_id    ),
        .in_req_valid_i ( refill_req_valid ),
        .in_req_ready_o ( refill_req_ready ),

        .in_rsp_data_o  ( refill_rsp_data  ),
        .in_rsp_error_o ( refill_rsp_error ),
        .in_rsp_id_o    ( refill_rsp_id    ),
        .in_rsp_valid_o ( refill_rsp_valid ),
        .in_rsp_ready_i ( refill_rsp_ready ),

        .refill_qaddr_o  ( refill_req.addr     ),
        .refill_qlen_o   ( refill_req.len      ),
        .refill_qvalid_o ( refill_qvalid       ),
        .refill_qready_i ( refill_qready       ),
        .refill_pdata_i  ( refill_resp_q.data  ),
        .refill_perror_i ( refill_resp_q.error ),
        .refill_plast_i  ( refill_resp_q.last  ),
        .refill_pvalid_i ( refill_pvalid_q     ),
        .refill_pready_o ( refill_pready_q     )
    );

    // Insert Slices.
    spill_register #(.T(refill_req_t)) i_spill_register_req (
        .clk_i,
        .rst_ni,
        .valid_i ( refill_qvalid   ),
        .ready_o ( refill_qready   ),
        .data_i  ( refill_req      ),
        // Q Output
        .valid_o ( refill_qvalid_o ),
        .ready_i ( refill_qready_i ),
        .data_o  ( refill_req_q    )
    );

    assign refill_qaddr_o = refill_req_q.addr;
    assign refill_qlen_o = refill_req_q.len;

    spill_register #(.T(refill_resp_t)) i_spill_register_resp (
        .clk_i,
        .rst_ni,
        .valid_i ( refill_pvalid_i ),
        .ready_o ( refill_pready_o ),
        .data_i  ( refill_resp     ),
        // Q Output
        .valid_o ( refill_pvalid_q ),
        .ready_i ( refill_pready_q ),
        .data_o  ( refill_resp_q   )
    );

    assign refill_resp.data = refill_pdata_i;
    assign refill_resp.error = refill_perror_i;
    assign refill_resp.last = refill_plast_i;
endmodule
