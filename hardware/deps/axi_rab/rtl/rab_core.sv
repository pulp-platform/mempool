// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// --=========================================================================--
//
// ██████╗  █████╗ ██████╗      ██████╗ ██████╗ ██████╗ ███████╗
// ██╔══██╗██╔══██╗██╔══██╗    ██╔════╝██╔═══██╗██╔══██╗██╔════╝
// ██████╔╝███████║██████╔╝    ██║     ██║   ██║██████╔╝█████╗
// ██╔══██╗██╔══██║██╔══██╗    ██║     ██║   ██║██╔══██╗██╔══╝
// ██║  ██║██║  ██║██████╔╝    ╚██████╗╚██████╔╝██║  ██║███████╗
// ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝      ╚═════╝ ╚═════╝ ╚═╝  ╚═╝╚══════╝
//
// --=========================================================================--

`define MY_ARRAY_SUM(MY_ARRAY,ARRAY_SIZE) ( (ARRAY_SIZE==1) ? MY_ARRAY[0] : (ARRAY_SIZE==2) ? MY_ARRAY[0] + MY_ARRAY[1] : (ARRAY_SIZE==3) ? MY_ARRAY[0] + MY_ARRAY[1] + MY_ARRAY[2] : (ARRAY_SIZE==4) ? MY_ARRAY[0] + MY_ARRAY[1] + MY_ARRAY[2] + MY_ARRAY[3] : 0 )

module rab_core
  #(
    parameter int unsigned N_PORTS             =  2,
    parameter int unsigned N_L1_SLICES [3:0]   = '{default: 0}, // number of L1 slices per port
    parameter int unsigned N_L1_SLICES_MAX     = 0, // maximum of per-port values above
    parameter bit          EN_ACP              = 0, // enable ACP
    parameter bit          ENABLE_L2TLB [3:0]  = '{default: 0}, // enable L2 TLB per port
    parameter int unsigned N_L2_SETS           = 32,
    parameter int unsigned N_L2_SET_ENTRIES    = 32,
    parameter int unsigned AXI_DATA_WIDTH      = 64,
    parameter int unsigned AXI_S_ADDR_WIDTH    = 32,
    parameter int unsigned AXI_M_ADDR_WIDTH    = 40,
    parameter int unsigned AXI_LITE_DATA_WIDTH = 64,
    parameter int unsigned AXI_LITE_ADDR_WIDTH = 32,
    parameter int unsigned AXI_ID_WIDTH        =  8,
    parameter int unsigned AXI_USER_WIDTH      =  6,
    parameter int unsigned MH_FIFO_DEPTH       = 16
    )
   (
    input  logic                                         Clk_CI,
    input  logic                                         Rst_RBI,

    input  logic               [AXI_LITE_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic                                         s_axi_awvalid,
    output logic                                         s_axi_awready,

    input  logic               [AXI_LITE_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic             [AXI_LITE_DATA_WIDTH/8-1:0] s_axi_wstrb,
    input  logic                                         s_axi_wvalid,
    output logic                                         s_axi_wready,

    input  logic               [AXI_LITE_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic                                         s_axi_arvalid,
    output logic                                         s_axi_arready,

    input  logic                                         s_axi_rready,
    output logic               [AXI_LITE_DATA_WIDTH-1:0] s_axi_rdata,
    output logic                                   [1:0] s_axi_rresp,
    output logic                                         s_axi_rvalid,

    output logic                                   [1:0] s_axi_bresp,
    output logic                                         s_axi_bvalid,
    input  logic                                         s_axi_bready,

    output logic [N_PORTS-1:0]                           int_miss,
    output logic [N_PORTS-1:0]                           int_prot,
    output logic [N_PORTS-1:0]                           int_multi,
    output logic [N_PORTS-1:0]                           int_prefetch,
    output logic [N_PORTS-1:0]                           int_invalidate,
    output logic                                         int_mhf_full,

    output logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] int_axaddr_min_o,
    output logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] int_axaddr_max_o,
    output logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] int_axid_o,
    output logic [N_PORTS-1:0]                     [7:0] int_axlen_o,
    output logic [N_PORTS-1:0]      [AXI_USER_WIDTH-1:0] int_axuser_o,

    input  logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] port1_addr,
    input  logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] port1_id,
    input  logic [N_PORTS-1:0]                     [7:0] port1_len,
    input  logic [N_PORTS-1:0]                     [2:0] port1_size,
    input  logic [N_PORTS-1:0]                           port1_addr_valid,
    input  logic [N_PORTS-1:0]                           port1_type,
    input  logic [N_PORTS-1:0]      [AXI_USER_WIDTH-1:0] port1_user,
    input  logic [N_PORTS-1:0]                           port1_sent,
    output logic [N_PORTS-1:0]    [AXI_M_ADDR_WIDTH-1:0] port1_out_addr,
    output logic [N_PORTS-1:0]                           port1_cache_coherent,
    output logic [N_PORTS-1:0]                           port1_accept,
    output logic [N_PORTS-1:0]                           port1_drop,
    output logic [N_PORTS-1:0]                           port1_miss,

    input  logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] port2_addr,
    input  logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] port2_id,
    input  logic [N_PORTS-1:0]                     [7:0] port2_len,
    input  logic [N_PORTS-1:0]                     [2:0] port2_size,
    input  logic [N_PORTS-1:0]                           port2_addr_valid,
    input  logic [N_PORTS-1:0]                           port2_type,
    input  logic [N_PORTS-1:0]      [AXI_USER_WIDTH-1:0] port2_user,
    input  logic [N_PORTS-1:0]                           port2_sent,
    output logic [N_PORTS-1:0]    [AXI_M_ADDR_WIDTH-1:0] port2_out_addr,
    output logic [N_PORTS-1:0]                           port2_cache_coherent,
    output logic [N_PORTS-1:0]                           port2_accept,
    output logic [N_PORTS-1:0]                           port2_drop,
    output logic [N_PORTS-1:0]                           port2_miss,

    input  logic [N_PORTS-1:0]                           miss_l2_i,
    input  logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] miss_l2_addr_i,
    input  logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] miss_l2_id_i,
    input  logic [N_PORTS-1:0]      [AXI_USER_WIDTH-1:0] miss_l2_user_i,

    output logic [N_PORTS-1:0] [AXI_LITE_DATA_WIDTH-1:0] wdata_l2_o,
    output logic [N_PORTS-1:0] [AXI_LITE_ADDR_WIDTH-1:0] waddr_l2_o,
    output logic [N_PORTS-1:0]                           wren_l2_o,

    input  logic [N_PORTS-1:0]                           invalidate_l2_done_i
    );

  // ███████╗██╗ ██████╗ ███╗   ██╗ █████╗ ██╗     ███████╗
  // ██╔════╝██║██╔════╝ ████╗  ██║██╔══██╗██║     ██╔════╝
  // ███████╗██║██║  ███╗██╔██╗ ██║███████║██║     ███████╗
  // ╚════██║██║██║   ██║██║╚██╗██║██╔══██║██║     ╚════██║
  // ███████║██║╚██████╔╝██║ ╚████║██║  ██║███████╗███████║
  // ╚══════╝╚═╝ ╚═════╝ ╚═╝  ╚═══╝╚═╝  ╚═╝╚══════╝╚══════╝
  //

  localparam N_L1_SLICES_TOT  = `MY_ARRAY_SUM(N_L1_SLICES, N_PORTS);

  localparam N_REGS           = 4*N_L1_SLICES_TOT + 4;
  localparam AXI_SIZE_WIDTH   = $clog2(AXI_DATA_WIDTH/8);

  localparam PORT_ID_WIDTH    = (N_PORTS < 2) ? 1 : $clog2(N_PORTS);
  localparam MISS_META_WIDTH  = PORT_ID_WIDTH + AXI_USER_WIDTH + AXI_ID_WIDTH;

  logic [N_PORTS-1:0]                      [15:0]     p1_burst_size;
  logic [N_PORTS-1:0]                      [15:0]     p2_burst_size;

  logic [N_PORTS-1:0]      [AXI_S_ADDR_WIDTH-1:0]     p1_align_addr;
  logic [N_PORTS-1:0]      [AXI_S_ADDR_WIDTH-1:0]     p2_align_addr;

  logic [N_PORTS-1:0]        [AXI_SIZE_WIDTH-1:0]     p1_mask;
  logic [N_PORTS-1:0]        [AXI_SIZE_WIDTH-1:0]     p2_mask;

  logic [N_PORTS-1:0]      [AXI_S_ADDR_WIDTH-1:0]     p1_max_addr;
  logic [N_PORTS-1:0]      [AXI_S_ADDR_WIDTH-1:0]     p2_max_addr;

  logic [N_PORTS-1:0]                                 p1_prefetch;
  logic [N_PORTS-1:0]                                 p2_prefetch;

  logic [N_PORTS-1:0]                                 int_rw;
  logic [N_PORTS-1:0]      [AXI_S_ADDR_WIDTH-1:0]     int_addr_min;
  logic [N_PORTS-1:0]      [AXI_S_ADDR_WIDTH-1:0]     int_addr_max;
  logic [N_PORTS-1:0]          [AXI_ID_WIDTH-1:0]     int_id;
  logic [N_PORTS-1:0]                       [7:0]     int_len;
  logic [N_PORTS-1:0]        [AXI_USER_WIDTH-1:0]     int_user;

  logic [N_PORTS-1:0]                                 hit;
  logic [N_PORTS-1:0]                                 prot;
  logic [N_PORTS-1:0]                                 prefetch;

  logic [N_PORTS-1:0]                                 no_hit;
  logic [N_PORTS-1:0]                                 no_prot;

  logic [N_PORTS-1:0]       [N_L1_SLICES_MAX-1:0]     hit_slices;
  logic [N_PORTS-1:0]       [N_L1_SLICES_MAX-1:0]     prot_slices;

  logic [N_PORTS-1:0]      [AXI_M_ADDR_WIDTH-1:0]     out_addr;
  logic [N_PORTS-1:0]      [AXI_M_ADDR_WIDTH-1:0]     out_addr_reg;

  logic [N_PORTS-1:0]                                 cache_coherent;
  logic [N_PORTS-1:0]                                 cache_coherent_reg;

  logic [N_PORTS-1:0]                                 select;
  reg   [N_PORTS-1:0]                                 curr_priority;

  reg   [N_PORTS-1:0]                                 multi_hit;

  logic [N_PORTS-1:0]                                 miss_valid_mhf;
  logic [N_PORTS-1:0]      [AXI_S_ADDR_WIDTH-1:0]     miss_addr_mhf;
  logic [N_PORTS-1:0]       [MISS_META_WIDTH-1:0]     miss_meta_mhf;

  logic [N_REGS-1:0]                       [63:0]     int_cfg_regs;
  logic [N_PORTS-1:0] [4*N_L1_SLICES_MAX-1:0] [63:0]  int_cfg_regs_slices;

  logic                                               L1AllowMultiHit_S;

  logic                                               invalidate_ready_q, invalidate_ready_d;
  logic [N_L1_SLICES_TOT-1:0]                         invalidate_slices;
  logic [AXI_S_ADDR_WIDTH-1:0]                        invalidate_addr_min;
  logic [AXI_S_ADDR_WIDTH-1:0]                        invalidate_addr_max;
  logic                                               invalidate_addr_valid;

  genvar z;

  //  █████╗ ███████╗███████╗██╗ ██████╗ ███╗   ██╗███╗   ███╗███████╗███╗   ██╗████████╗███████╗
  // ██╔══██╗██╔════╝██╔════╝██║██╔════╝ ████╗  ██║████╗ ████║██╔════╝████╗  ██║╚══██╔══╝██╔════╝
  // ███████║███████╗███████╗██║██║  ███╗██╔██╗ ██║██╔████╔██║█████╗  ██╔██╗ ██║   ██║   ███████╗
  // ██╔══██║╚════██║╚════██║██║██║   ██║██║╚██╗██║██║╚██╔╝██║██╔══╝  ██║╚██╗██║   ██║   ╚════██║
  // ██║  ██║███████║███████║██║╚██████╔╝██║ ╚████║██║ ╚═╝ ██║███████╗██║ ╚████║   ██║   ███████║
  // ╚═╝  ╚═╝╚══════╝╚══════╝╚═╝ ╚═════╝ ╚═╝  ╚═══╝╚═╝     ╚═╝╚══════╝╚═╝  ╚═══╝   ╚═╝   ╚══════╝
  //

  assign invalidate_o = invalidate_addr_valid;

  always_comb
    begin : PORT_SELECT
      var integer idx, idx_slice, idx_tot;
      idx_tot = 0;

      invalidate_slices = 'b0;
      // records to invalidate are available in a single cycle
      invalidate_ready_d = invalidate_addr_valid;

      for (idx=0; idx<N_PORTS; idx++) begin

        p1_burst_size[idx] = (port1_len[idx] + 1) << port1_size[idx];
        p2_burst_size[idx] = (port2_len[idx] + 1) << port2_size[idx];

        // align min addr for max addr computation to allow for smart AXI bursts around the 4k boundary
        if      (port1_size[idx] == 3'b001)
          p1_mask[idx] = 3'b110;
        else if (port1_size[idx] == 3'b010)
          p1_mask[idx] = 3'b100;
        else if (port1_size[idx] == 3'b011)
          p1_mask[idx] = 3'b000;
        else
          p1_mask[idx] = 3'b111;

        p1_align_addr[idx][AXI_S_ADDR_WIDTH-1:AXI_SIZE_WIDTH] = port1_addr[idx][AXI_S_ADDR_WIDTH-1:AXI_SIZE_WIDTH];
        p1_align_addr[idx][AXI_SIZE_WIDTH-1:0]                = port1_addr[idx][AXI_SIZE_WIDTH-1:0] & p1_mask[idx];

        if      (port2_size[idx] == 3'b001)
          p2_mask[idx] = 3'b110;
        else if (port2_size[idx] == 3'b010)
          p2_mask[idx] = 3'b100;
        else if (port2_size[idx] == 3'b011)
          p2_mask[idx] = 3'b000;
        else
          p2_mask[idx] = 3'b111;

        if (port1_user[idx] == {AXI_USER_WIDTH{1'b1}})
          p1_prefetch[idx] = 1'b1;
        else
          p1_prefetch[idx] = 1'b0;

        if (port2_user[idx] == {AXI_USER_WIDTH{1'b1}})
          p2_prefetch[idx] = 1'b1;
        else
          p2_prefetch[idx] = 1'b0;

        p2_align_addr[idx][AXI_S_ADDR_WIDTH-1:AXI_SIZE_WIDTH] = port2_addr[idx][AXI_S_ADDR_WIDTH-1:AXI_SIZE_WIDTH];
        p2_align_addr[idx][AXI_SIZE_WIDTH-1:0]                = port2_addr[idx][AXI_SIZE_WIDTH-1:0] & p2_mask[idx];

        p1_max_addr[idx]  = p1_align_addr[idx] + p1_burst_size[idx] - 1;
        p2_max_addr[idx]  = p2_align_addr[idx] + p2_burst_size[idx] - 1;


        select[idx]       = 'b0;
        int_rw[idx]       = 'b0;
        int_id[idx]       = 'b0;
        int_len[idx]      = 'b0;
        int_user[idx]     = 'b0;
        prefetch[idx]     = 'b0;

        if ( invalidate_addr_valid ) begin
          int_addr_min[idx] = invalidate_addr_min;
          int_addr_max[idx] = invalidate_addr_max;

          for (idx_slice = 0; idx_slice<N_L1_SLICES[idx]; ++idx_slice) begin
            invalidate_slices[idx_tot] = hit_slices[idx][idx_slice];
            ++idx_tot;
          end
        end else begin
          // select = 1 -> port1 active
          // select = 0 -> port2 active
          select[idx] = (curr_priority[idx] & port1_addr_valid[idx]) | ~port2_addr_valid[idx];

          int_addr_min[idx] = select[idx] ? port1_addr[idx]  : port2_addr[idx];
          int_addr_max[idx] = select[idx] ? p1_max_addr[idx] : p2_max_addr[idx];
          int_rw[idx]       = select[idx] ? port1_type[idx]  : port2_type[idx];
          int_id[idx]       = select[idx] ? port1_id[idx]    : port2_id[idx];
          int_len[idx]      = select[idx] ? port1_len[idx]   : port2_len[idx];
          int_user[idx]     = select[idx] ? port1_user[idx]  : port2_user[idx];
          prefetch[idx]     = select[idx] ? p1_prefetch[idx] : p2_prefetch[idx];
        end

        hit [idx]    = | hit_slices [idx];
        prot[idx]    = | prot_slices[idx];

        no_hit [idx] = ~hit [idx];
        no_prot[idx] = ~prot[idx];

        port1_out_addr[idx] = out_addr_reg[idx];
        port2_out_addr[idx] = out_addr_reg[idx];

        port1_cache_coherent[idx] = cache_coherent_reg[idx];
        port2_cache_coherent[idx] = cache_coherent_reg[idx];
      end
    end

  always_comb
    begin
      var integer idx_port, idx_slice;
      var integer reg_num;
      reg_num=0;
      for ( idx_port = 0; idx_port < N_PORTS; idx_port++ ) begin
        for ( idx_slice = 0; idx_slice < 4*N_L1_SLICES[idx_port]; idx_slice++ ) begin
          int_cfg_regs_slices[idx_port][idx_slice] = int_cfg_regs[4+reg_num];
          reg_num++;
        end
        // int_cfg_regs_slices[idx_port][N_L1_SLICES_MAX:N_L1_SLICES[idx_port]] will be dangling
        // Fix to zero. Synthesis will remove these signals.
        // int_cfg_regs_slices[idx_port][4*N_L1_SLICES_MAX-1:4*N_L1_SLICES[idx_port]] = 0;
      end
    end

  // set invalidate ready after invalidation slices are available
  always_ff @(posedge Clk_CI or negedge Rst_RBI) begin
    if (Rst_RBI == 1'b0) begin
        invalidate_ready_q <= 'b0;
      end else begin
        invalidate_ready_q <= invalidate_ready_d;
      end
  end

  // save port priority (only used if invalidation port is not set)
  always @(posedge Clk_CI or negedge Rst_RBI)
    begin : PORT_PRIORITY
      var integer idx;
      if (Rst_RBI == 1'b0) begin
        curr_priority <= 'h0;
      end else begin
        for (idx=0; idx<N_PORTS; idx++) begin
          if (port1_accept[idx] || port1_drop[idx])
            curr_priority[idx] <= 1'b1;
          else if (port2_accept[idx] || port2_drop[idx])
            curr_priority[idx] <= 1'b0;
        end
      end
    end

  // find port that misses
  logic [PORT_ID_WIDTH-1:0] PortIdx_D; // index of the first missing port
  var integer               idx_miss;
  always_comb begin : MHF_PORT_SELECT
    PortIdx_D = 'b0;
    for (idx_miss = 0; idx_miss < N_PORTS; idx_miss++) begin
      if (miss_valid_mhf[idx_miss] == 1'b1) begin
        PortIdx_D = idx_miss;
        break;
      end
    end
  end // always_comb begin

  //  █████╗ ██╗  ██╗██╗    ██████╗  █████╗ ██████╗      ██████╗███████╗ ██████╗
  // ██╔══██╗╚██╗██╔╝██║    ██╔══██╗██╔══██╗██╔══██╗    ██╔════╝██╔════╝██╔════╝
  // ███████║ ╚███╔╝ ██║    ██████╔╝███████║██████╔╝    ██║     █████╗  ██║  ███╗
  // ██╔══██║ ██╔██╗ ██║    ██╔══██╗██╔══██║██╔══██╗    ██║     ██╔══╝  ██║   ██║
  // ██║  ██║██╔╝ ██╗██║    ██║  ██║██║  ██║██████╔╝    ╚██████╗██║     ╚██████╔╝
  // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝    ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝      ╚═════╝╚═╝      ╚═════╝
  //
  axi_rab_cfg
    #(
      .N_PORTS         ( N_PORTS             ),
      .N_REGS          ( N_REGS              ),
      .N_SLICES_TOT    ( N_L1_SLICES_TOT     ),
      .N_L2_SETS       ( N_L2_SETS           ),
      .N_L2_SET_ENTRIES( N_L2_SET_ENTRIES    ),
      .ADDR_WIDTH_PHYS ( AXI_M_ADDR_WIDTH    ),
      .ADDR_WIDTH_VIRT ( AXI_S_ADDR_WIDTH    ),
      .N_FLAGS         ( 4                   ),
      .AXI_DATA_WIDTH  ( AXI_LITE_DATA_WIDTH ),
      .AXI_ADDR_WIDTH  ( AXI_LITE_ADDR_WIDTH ),
      .MISS_META_WIDTH ( MISS_META_WIDTH     ),
      .MH_FIFO_DEPTH   ( MH_FIFO_DEPTH       )
    )
    u_axi_rab_cfg
    (
      .Clk_CI                  ( Clk_CI                    ),
      .Rst_RBI                 ( Rst_RBI                   ),
      .s_axi_awaddr            ( s_axi_awaddr              ),
      .s_axi_awvalid           ( s_axi_awvalid             ),
      .s_axi_wdata             ( s_axi_wdata               ),
      .s_axi_wstrb             ( s_axi_wstrb               ),
      .s_axi_wvalid            ( s_axi_wvalid              ),
      .s_axi_bready            ( s_axi_bready              ),
      .s_axi_araddr            ( s_axi_araddr              ),
      .s_axi_arvalid           ( s_axi_arvalid             ),
      .s_axi_rready            ( s_axi_rready              ),
      .s_axi_arready           ( s_axi_arready             ),
      .s_axi_rdata             ( s_axi_rdata               ),
      .s_axi_rresp             ( s_axi_rresp               ),
      .s_axi_rvalid            ( s_axi_rvalid              ),
      .s_axi_wready            ( s_axi_wready              ),
      .s_axi_bresp             ( s_axi_bresp               ),
      .s_axi_bvalid            ( s_axi_bvalid              ),
      .s_axi_awready           ( s_axi_awready             ),
      .L1Cfg_DO                ( int_cfg_regs              ),
      .L1AllowMultiHit_SO      ( L1AllowMultiHit_S         ),
      .MissAddr_DI             ( miss_addr_mhf[PortIdx_D]  ),
      .MissMeta_DI             ( miss_meta_mhf[PortIdx_D]  ),
      .Miss_SI                 ( miss_valid_mhf[PortIdx_D] ),
      .MhFifoFull_SO           ( int_mhf_full              ),
      .wdata_l2                ( wdata_l2_o                ),
      .waddr_l2                ( waddr_l2_o                ),
      .wren_l2                 ( wren_l2_o                 ),
      .l1_invalidate_ready_i   ( invalidate_ready_q        ),
      .l1_invalidate_slices_i  ( invalidate_slices         ),
      .l2_invalidate_done_i    ( invalidate_l2_done_i      ),
      .invalidate_addr_min_o   ( invalidate_addr_min       ),
      .invalidate_addr_max_o   ( invalidate_addr_max       ),
      .invalidate_addr_valid_o ( invalidate_addr_valid     )
    );

  generate for (z = 0; z < N_PORTS; z++) begin : MHF_TLB_SELECT
    if (ENABLE_L2TLB[z]) begin // L2 TLB is enabled
      assign miss_valid_mhf[z] = miss_l2_i[z];
      assign miss_addr_mhf[z]  = miss_l2_addr_i[z];
      assign miss_meta_mhf[z]  = {miss_l2_user_i[z], PortIdx_D, miss_l2_id_i[z]};
    end else begin// L2 TLB is disabled
      assign miss_valid_mhf[z] = int_miss[z];
      assign miss_addr_mhf[z]  = int_addr_min[z];
      assign miss_meta_mhf[z]  = {int_user[z], PortIdx_D, int_id[z]};
    end
  end
  endgenerate

  // ███████╗██╗     ██╗ ██████╗███████╗    ████████╗ ██████╗ ██████╗
  // ██╔════╝██║     ██║██╔════╝██╔════╝    ╚══██╔══╝██╔═══██╗██╔══██╗
  // ███████╗██║     ██║██║     █████╗         ██║   ██║   ██║██████╔╝
  // ╚════██║██║     ██║██║     ██╔══╝         ██║   ██║   ██║██╔═══╝
  // ███████║███████╗██║╚██████╗███████╗       ██║   ╚██████╔╝██║
  // ╚══════╝╚══════╝╚═╝ ╚═════╝╚══════╝       ╚═╝    ╚═════╝ ╚═╝
  //
  generate for (z = 0; z < N_PORTS; z++) begin : SLICE_TOP_GEN
    slice_top
      #(
        .N_SLICES        ( N_L1_SLICES[z]   ),
        .N_REGS          ( 4*N_L1_SLICES[z] ),
        .ADDR_WIDTH_PHYS ( AXI_M_ADDR_WIDTH ),
        .ADDR_WIDTH_VIRT ( AXI_S_ADDR_WIDTH )
      )
      u_slice_top
      (
        .int_cfg_regs        ( int_cfg_regs_slices[z][4*N_L1_SLICES[z]-1:0] ),
        .int_rw              ( int_rw[z]                                   ),
        .int_addr_min        ( int_addr_min[z]                             ),
        .int_addr_max        ( int_addr_max[z]                             ),
        .partial_match_allow ( invalidate_addr_valid                       ),
        .multi_hit_allow     ( L1AllowMultiHit_S                           ),
        .multi_hit           ( multi_hit[z]                                ),
        .prot                ( prot_slices[z][N_L1_SLICES[z]-1:0]          ),
        .hit                 ( hit_slices [z][N_L1_SLICES[z]-1:0]          ),
        .cache_coherent      ( cache_coherent[z]                           ),
        .out_addr            ( out_addr[z]                                 )
      );
    // hit_slices [N_L1_SLICES_MAX-1:N_L1_SLICES_MAX-N_L1_SLICES[z]] will be dangling
    // prot_slices[N_L1_SLICES_MAX-1:N_L1_SLICES_MAX-N_L1_SLICES[z]] will be dangling
    // Fix to zero. Synthesis will remove these signals.
    if ( N_L1_SLICES[z] < N_L1_SLICES_MAX ) begin
      assign hit_slices [z][N_L1_SLICES_MAX-1:N_L1_SLICES[z]] = 0;
      assign prot_slices[z][N_L1_SLICES_MAX-1:N_L1_SLICES[z]] = 0;
    end
  end // for (z = 0; z < N_PORTS; z++)
  endgenerate

  // ███████╗███████╗███╗   ███╗
  // ██╔════╝██╔════╝████╗ ████║
  // █████╗  ███████╗██╔████╔██║
  // ██╔══╝  ╚════██║██║╚██╔╝██║
  // ██║     ███████║██║ ╚═╝ ██║
  // ╚═╝     ╚══════╝╚═╝     ╚═╝
  //
  generate for (z = 0; z < N_PORTS; z++) begin : FSM_GEN
    fsm
      #(
        .AXI_M_ADDR_WIDTH ( AXI_M_ADDR_WIDTH ),
        .AXI_S_ADDR_WIDTH ( AXI_S_ADDR_WIDTH ),
        .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
      )
      u_fsm
      (
        .Clk_CI             ( Clk_CI                           ),
        .Rst_RBI            ( Rst_RBI                          ),
        .port1_addr_valid_i ( port1_addr_valid[z]              ),
        .port2_addr_valid_i ( port2_addr_valid[z]              ),
        .port1_sent_i       ( port1_sent[z]                    ),
        .port2_sent_i       ( port2_sent[z]                    ),
        .select_i           ( select[z]                        ),
        .invalidate_i       ( invalidate_addr_valid            ),
        .no_hit_i           ( no_hit[z]                        ),
        .multi_hit_i        ( multi_hit[z]                     ),
        .no_prot_i          ( no_prot[z]                       ),
        .prefetch_i         ( prefetch[z]                      ),
        .out_addr_i         ( out_addr[z]                      ),
        .cache_coherent_i   ( cache_coherent[z]                ),
        .port1_accept_o     ( port1_accept[z]                  ),
        .port1_drop_o       ( port1_drop[z]                    ),
        .port1_miss_o       ( port1_miss[z]                    ),
        .port2_accept_o     ( port2_accept[z]                  ),
        .port2_drop_o       ( port2_drop[z]                    ),
        .port2_miss_o       ( port2_miss[z]                    ),
        .out_addr_o         ( out_addr_reg[z]                  ),
        .cache_coherent_o   ( cache_coherent_reg[z]            ),
        .miss_o             ( int_miss[z]                      ),
        .multi_o            ( int_multi[z]                     ),
        .prot_o             ( int_prot[z]                      ),
        .prefetch_o         ( int_prefetch[z]                  ),
        .invalidate_o       ( int_invalidate[z]                ),
        .in_addr_min_i      ( int_addr_min[z]                  ),
        .in_addr_max_i      ( int_addr_max[z]                  ),
        .in_id_i            ( int_id[z]                        ),
        .in_len_i           ( int_len[z]                       ),
        .in_user_i          ( int_user[z]                      ),
        .in_addr_min_o      ( int_axaddr_min_o[z]              ),
        .in_addr_max_o      ( int_axaddr_max_o[z]              ),
        .in_id_o            ( int_axid_o[z]                    ),
        .in_len_o           ( int_axlen_o[z]                   ),
        .in_user_o          ( int_axuser_o[z]                  )
      );
  end
  endgenerate

endmodule
