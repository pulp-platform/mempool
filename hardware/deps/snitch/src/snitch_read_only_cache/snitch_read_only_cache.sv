// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
//         Samuel Riedel <sriedel@iis.ee.ethz.ch>


/// Serve bufferable read memory requests from a constant cache.
/// In more specific AXI terms:
///   ArCache xy11 (x or y must be 1)
///   - ArCache[3] (OtherAllocate)
///   - ArCache[2] (Allocate)
///   - ArCache[1] (Modifiable): Must be 1
///   - ArCache[0] (Bufferable): Must be 1
///
/// Other reads will be served from backing memory.
/// Write requests must always be non-bufferable and non-cacheable.
/// i.e., AwCache must be 00?0
module snitch_read_only_cache #(
  /// Cache Line Width
  parameter int unsigned LineWidth = -1,
  /// The number of cache lines per set. Power of two; >= 2.
  parameter int unsigned LineCount = -1,
  /// The set associativity of the cache. Power of two; >= 1.
  parameter int unsigned SetCount = 1,
  /// AXI address width
  parameter int unsigned AxiAddrWidth = 0,
  /// AXI data width
  parameter int unsigned AxiDataWidth = 0,
  /// AXI id width
  parameter int unsigned AxiIdWidth = 0,
  /// AXI user width
  parameter int unsigned AxiUserWidth = 0,
  parameter int unsigned MaxTrans       = 32'd8,
  parameter int unsigned NrAddrRules = 1,
  parameter type slv_req_t = logic,
  parameter type slv_rsp_t = logic,
  parameter type mst_req_t = logic,
  parameter type mst_rsp_t = logic
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic enable_i,
  input  logic flush_valid_i,
  output logic flush_ready_o,
  input  logic [AxiAddrWidth-1:0] start_addr_i [NrAddrRules],
  input  logic [AxiAddrWidth-1:0] end_addr_i [NrAddrRules],
  input  slv_req_t axi_slv_req_i,
  output slv_rsp_t axi_slv_rsp_o,
  output mst_req_t axi_mst_req_o,
  input  mst_rsp_t axi_mst_rsp_i
);

  `include "axi/typedef.svh"
  `include "common_cells/registers.svh"
  import cf_math_pkg::idx_width;

  // Check for supported parameters
  if (AxiDataWidth < 32)
    $error("snitch_const_cache: AxiDataWidth must be larger than 32.");
  if (AxiDataWidth > LineWidth)
    $error("snitch_const_cache: LineWidth must be larger/equal than AxiDataWidth.");

  typedef enum logic [1:0] {
    Error = 0,
    Cache = 1,
    Bypass = 2
  } index_e;

  typedef logic [AxiIdWidth-1:0] id_t;
  typedef logic [AxiIdWidth:0] mst_id_t;
  typedef logic [AxiAddrWidth-1:0] addr_t;
  typedef logic [AxiDataWidth-1:0] data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic [AxiUserWidth-1:0] user_t;

  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(axi_mst, addr_t, mst_id_t, data_t, strb_t, user_t)

  axi_req_t [2:0] demux_req;
  axi_resp_t [2:0] demux_rsp;

  axi_req_t refill_req;
  axi_resp_t refill_rsp;

  logic [1:0] slv_aw_select;
  logic [1:0] slv_ar_select;

  axi_demux #(
    .AxiIdWidth     ( AxiIdWidth    ),
    .aw_chan_t      ( axi_aw_chan_t ),
    .w_chan_t       ( axi_w_chan_t  ),
    .b_chan_t       ( axi_b_chan_t  ),
    .ar_chan_t      ( axi_ar_chan_t ),
    .r_chan_t       ( axi_r_chan_t  ),
    .req_t          ( axi_req_t     ),
    .resp_t         ( axi_resp_t    ),
    .NoMstPorts     ( 3             ),
    .MaxTrans       ( MaxTrans      ),
    .AxiLookBits    ( AxiIdWidth    ),
    .FallThrough    ( 1'b1          ),
    .SpillAw        ( 1'b0          ),
    .SpillW         ( 1'b0          ),
    .SpillB         ( 1'b0          ),
    .SpillAr        ( 1'b0          ),
    .SpillR         ( 1'b0          )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i          ( 1'b0                ),
    .slv_req_i       ( axi_slv_req_i       ),
    .slv_aw_select_i ( slv_aw_select       ),
    .slv_ar_select_i ( slv_ar_select       ),
    .slv_resp_o      ( axi_slv_rsp_o       ),
    .mst_reqs_o      ( demux_req           ),
    .mst_resps_i     ( demux_rsp           )
  );

  axi_err_slv #(
    .AxiIdWidth  ( AxiIdWidth ),
    .req_t       ( axi_req_t              ),
    .resp_t      ( axi_resp_t             ),
    .Resp        ( axi_pkg::RESP_DECERR   ),
    .ATOPs       ( 1'b1                   ),
    .MaxTrans    ( 1                      )
  ) i_axi_err_slv (
    .clk_i,
    .rst_ni,
    .test_i (1'b0),
    // slave port
    .slv_req_i  ( demux_req[0] ),
    .slv_resp_o ( demux_rsp[0] )
  );

  logic [1:0] dec_ar;

  typedef struct packed {
    int unsigned idx;
    addr_t       start_addr;
    addr_t       end_addr;
  } rule_t;

  rule_t [NrAddrRules-1:0] addr_map;

  for (genvar i = 0; i < NrAddrRules; i++) begin : gen_addr_map
    assign addr_map[i] = '{
      idx: Cache,
      start_addr: start_addr_i[i],
      end_addr: end_addr_i[i]
    };
  end

  addr_decode #(
    .NoIndices  ( 3 ),
    .NoRules    ( NrAddrRules ),
    .addr_t     ( addr_t ),
    .rule_t     ( rule_t )
  ) i_axi_aw_decode (
    .addr_i           ( axi_slv_req_i.ar.addr ),
    .addr_map_i       ( addr_map              ),
    .idx_o            ( dec_ar                ),
    .dec_valid_o      (                       ),
    .dec_error_o      (                       ),
    .en_default_idx_i ( 1'b1                  ),
    // Default is bypass.
    .default_idx_i    ( Bypass                )
  );

  // `AW` always bypass
  assign slv_aw_select = Bypass;

  // select logic
  always_comb begin
    // Cache selection logic.
    slv_ar_select = dec_ar;
    // Bypass all atomic requests
    if (axi_slv_req_i.ar.lock) begin
      slv_ar_select = Bypass;
    end
    // Wrapping bursts are currently not supported.
    if (axi_slv_req_i.ar.burst == axi_pkg::BURST_WRAP) begin
      slv_ar_select = Bypass;
    end
    // Bypass cache if disabled
    if (enable_i == 1'b0) begin
      slv_ar_select = Bypass;
    end
  end

  // Store some AXI metadata for the response
  typedef struct packed {
    logic [AxiIdWidth-1:0]          id; // Store the AXI ID of the request
    logic [$clog2(LineWidth/8)-1:0] addr; // Store the offset in the cache line minus the byte offset
    axi_pkg::len_t                  len; // Store the length of the burst
    axi_pkg::size_t                 size; // Store the size of the beats
    logic                           valid; // Metadata is valid --> a transaction is already in flight
  } metadata_t;

  localparam PendingCount = 2**AxiIdWidth; // TODO: Necessary for now to support all IDs requesting the same address in the handler

  localparam snitch_icache_pkg::config_t CFG = '{
      LINE_WIDTH:    LineWidth,
      LINE_COUNT:    LineCount,
      SET_COUNT:     SetCount,
      PENDING_COUNT: PendingCount,
      FETCH_AW:      AxiAddrWidth,
      FETCH_DW:      AxiDataWidth,
      FILL_AW:       AxiAddrWidth,
      FILL_DW:       AxiDataWidth,

      FETCH_ALIGN:   $clog2(AxiDataWidth/8),
      FILL_ALIGN:    $clog2(AxiDataWidth/8),
      LINE_ALIGN:    $clog2(LineWidth/8),
      COUNT_ALIGN:   cf_math_pkg::idx_width(LineCount),
      SET_ALIGN:     cf_math_pkg::idx_width(SetCount),
      TAG_WIDTH:     AxiAddrWidth - $clog2(LineWidth/8) - $clog2(LineCount) + 1,
      ID_WIDTH_REQ:  AxiIdWidth,
      ID_WIDTH_RESP: 2**AxiIdWidth,
      META_WIDTH:    $bits(metadata_t),
      PENDING_IW:    $clog2(PendingCount),
      default:       0
  };

  // The lookup module contains the actual cache RAMs and performs lookups.
  logic [CFG.FETCH_AW-1:0]     lookup_addr;
  metadata_t                   lookup_meta;
  logic [CFG.SET_ALIGN-1:0]    lookup_set;
  logic                        lookup_hit;
  logic [CFG.LINE_WIDTH-1:0]   lookup_data;
  logic                        lookup_error;
  logic                        lookup_valid;
  logic                        lookup_ready;

  logic [CFG.COUNT_ALIGN-1:0]  write_addr;
  logic [CFG.SET_ALIGN-1:0]    write_set;
  logic [CFG.LINE_WIDTH-1:0]   write_data;
  logic [CFG.TAG_WIDTH-1:0]    write_tag;
  logic                        write_error;
  logic                        write_valid;
  logic                        write_ready;

  logic [CFG.FETCH_AW-1:0]     in_addr;
  metadata_t                   in_meta;
  logic                        in_valid;
  logic                        in_ready;

  logic                         handler_req_valid;
  logic                         handler_req_ready;
  logic [CFG.FETCH_AW-1:0]      handler_req_addr;
  logic [CFG.PENDING_IW-1:0]    handler_req_id;

  logic [CFG.LINE_WIDTH-1:0]    handler_rsp_data;
  logic                         handler_rsp_error;
  logic [CFG.PENDING_IW-1:0]    handler_rsp_id;
  logic                         handler_rsp_valid;
  logic                         handler_rsp_ready;

  logic [CFG.LINE_WIDTH-1:0]    in_rsp_data;
  logic                         in_rsp_error;
  logic [CFG.ID_WIDTH_RESP-1:0] in_rsp_id;
  logic                         in_rsp_valid;
  logic                         in_rsp_ready;

  localparam int unsigned MaxTxns = 8;

  snitch_axi_to_cache #(
    .MaxTxns     ( MaxTxns      ),
    .AddrWidth   ( 0            ),
    .DataWidth   ( 0            ),
    .IdWidth     ( AxiIdWidth   ),
    .UserWidth   ( 0            ),
    .metadata_t  ( metadata_t   ),
    .req_t       ( axi_req_t    ),
    .resp_t      ( axi_resp_t   ),
    .CFG         ( CFG          )
  ) i_axi_to_cache (
    .clk_i       ( clk_i        ),
    .rst_ni      ( rst_ni       ),
    // Cache request
    .req_addr_o  ( in_addr      ),
    .req_meta_o  ( in_meta      ),
    .req_valid_o ( in_valid     ),
    .req_ready_i ( in_ready     ),
    // Cache response
    .rsp_data_i  ( in_rsp_data  ),
    .rsp_error_i ( in_rsp_error ),
    .rsp_id_i    ( in_rsp_id    ),
    .rsp_meta_i  ( in_rsp_id    ),
    .rsp_valid_i ( in_rsp_valid ),
    .rsp_ready_o ( in_rsp_ready ),
    // AXI
    .slv_req_i   ( demux_req[Cache] ),
    .slv_rsp_o   ( demux_rsp[Cache] )
  );

  snitch_icache_lookup_parallel #(CFG) i_lookup (
    .clk_i,
    .rst_ni,

    .flush_valid_i ( flush_valid_i ),
    .flush_ready_o ( flush_ready_o ),

    .in_addr_i     ( in_addr   ),
    .in_meta_i     ( in_meta   ),
    .in_valid_i    ( in_valid  ),
    .in_ready_o    ( in_ready  ),

    .out_addr_o    ( lookup_addr        ),
    .out_meta_o    ( lookup_meta        ),
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

  snitch_icache_handler #(CFG) i_handler (
    .clk_i,
    .rst_ni,

    .in_req_addr_i   ( lookup_addr        ),
    .in_req_id_i     ( lookup_meta.id     ),
    .in_req_set_i    ( lookup_set         ),
    .in_req_hit_i    ( lookup_hit         ),
    .in_req_data_i   ( lookup_data        ),
    .in_req_error_i  ( lookup_error       ),
    .in_req_valid_i  ( lookup_valid       ),
    .in_req_ready_o  ( lookup_ready       ),

    .in_rsp_data_o   ( in_rsp_data        ),
    .in_rsp_error_o  ( in_rsp_error       ),
    .in_rsp_id_o     ( in_rsp_id          ),
    .in_rsp_valid_o  ( in_rsp_valid       ),
    .in_rsp_ready_i  ( in_rsp_ready       ),

    .write_addr_o    ( write_addr         ),
    .write_set_o     ( write_set          ),
    .write_data_o    ( write_data         ),
    .write_tag_o     ( write_tag          ),
    .write_error_o   ( write_error        ),
    .write_valid_o   ( write_valid        ),
    .write_ready_i   ( write_ready        ),

    .out_req_addr_o  ( handler_req_addr   ),
    .out_req_id_o    ( handler_req_id     ),
    .out_req_valid_o ( handler_req_valid  ),
    .out_req_ready_i ( handler_req_ready  ),

    .out_rsp_data_i  ( handler_rsp_data   ),
    .out_rsp_error_i ( handler_rsp_error  ),
    .out_rsp_id_i    ( handler_rsp_id     ),
    .out_rsp_valid_i ( handler_rsp_valid  ),
    .out_rsp_ready_o ( handler_rsp_ready  )
  );

  // Instantiate the cache refill module which emits AXI transactions.
  snitch_icache_refill #(
    .CFG(CFG),
    .axi_req_t (axi_req_t),
    .axi_rsp_t (axi_resp_t)
  ) i_refill (
    .clk_i,
    .rst_ni,

    .in_req_addr_i   ( handler_req_addr  ),
    .in_req_id_i     ( handler_req_id    ),
    .in_req_bypass_i ( 1'b0              ),
    .in_req_valid_i  ( handler_req_valid ),
    .in_req_ready_o  ( handler_req_ready ),

    .in_rsp_data_o   ( handler_rsp_data   ),
    .in_rsp_error_o  ( handler_rsp_error  ),
    .in_rsp_id_o     ( handler_rsp_id     ),
    .in_rsp_bypass_o ( /* left open */    ),
    .in_rsp_valid_o  ( handler_rsp_valid  ),
    .in_rsp_ready_i  ( handler_rsp_ready  ),
    .axi_req_o (refill_req),
    .axi_rsp_i (refill_rsp)
  );

  axi_mux #(
    .SlvAxiIDWidth ( AxiIdWidth ),
    .slv_aw_chan_t ( axi_aw_chan_t ),
    .mst_aw_chan_t ( axi_mst_aw_chan_t ),
    .w_chan_t      ( axi_w_chan_t ),
    .slv_b_chan_t  ( axi_b_chan_t ),
    .mst_b_chan_t  ( axi_mst_b_chan_t ),
    .slv_ar_chan_t ( axi_ar_chan_t ),
    .mst_ar_chan_t ( axi_mst_ar_chan_t ),
    .slv_r_chan_t  ( axi_r_chan_t ),
    .mst_r_chan_t  ( axi_mst_r_chan_t ),
    .slv_req_t     ( axi_req_t ),
    .slv_resp_t    ( axi_resp_t ),
    .mst_req_t     ( axi_mst_req_t ),
    .mst_resp_t    ( axi_mst_resp_t ),
    .NoSlvPorts    ( 2 ),
    .MaxWTrans     ( MaxTrans ),
    .FallThrough   ( 1'b1 ),
    .SpillAw       ( 1'b0 ),
    .SpillW        ( 1'b0 ),
    .SpillB        ( 1'b0 ),
    .SpillAr       ( 1'b0 ),
    .SpillR        ( 1'b0 )
  ) i_axi_mux (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .test_i (1'b0),  // Test Mode enable
    .slv_reqs_i  ({demux_req[2], refill_req}),
    .slv_resps_o ({demux_rsp[2], refill_rsp}),
    .mst_req_o   (axi_mst_req_o),
    .mst_resp_i  (axi_mst_rsp_i)
  );

endmodule
