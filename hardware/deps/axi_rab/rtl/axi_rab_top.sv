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
//  █████╗ ██╗  ██╗██╗    ██████╗  █████╗ ██████╗     ████████╗ ██████╗ ██████╗
// ██╔══██╗╚██╗██╔╝██║    ██╔══██╗██╔══██╗██╔══██╗    ╚══██╔══╝██╔═══██╗██╔══██╗
// ███████║ ╚███╔╝ ██║    ██████╔╝███████║██████╔╝       ██║   ██║   ██║██████╔╝
// ██╔══██║ ██╔██╗ ██║    ██╔══██╗██╔══██║██╔══██╗       ██║   ██║   ██║██╔═══╝
// ██║  ██║██╔╝ ██╗██║    ██║  ██║██║  ██║██████╔╝       ██║   ╚██████╔╝██║
// ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝    ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝        ╚═╝    ╚═════╝ ╚═╝
//
// --=========================================================================--
/*
 * axi_rab_top
 *
 * The remapping address block (RAB) performs address translation for AXI
 * transactions arriving at the input port and forwards them to different
 * downstream AXI ports.
 *
 * The five axi channels are each buffered on the input side using a FIFO,
 * described in axi4_XX_buffer. The RAB lookup result is merged into the
 * AXI transaction via the axi4_XX_sender instances, which manages upstream
 * error signaling for failed lookups.
 *
 * Address translation is performed based on data stored in up to two
 * translation lookaside buffers (TLBs), which are private per RAB port (each
 * of which having two AXI master ports and one AXI slave port). These TLBs
 * are managed in software through the AXI-Lite interface.
 *
 * If ACP is enabled, the `cache_coherent` flag in the TLBs is used to
 * multiplex between the two ports. If ACP is disabled, only the first master
 * port is used. In this case, the `cache_coherent` flag is used to set the
 * AxCACHE signals of the AXI bus accordingly.
 *
 * Authors:
 * Antonio Pullini <pullinia@iis.ee.ethz.ch>
 * Conrad Burchert <bconrad@ethz.ch>
 * Maheshwara Sharma <msharma@student.ethz.ch>
 * Andreas Kurth <akurth@iis.ee.ethz.ch>
 * Johannes Weinbuch <jweinbuch@student.ethz.ch>
 * Koen Wolters <kwolters@student.ethz.ch>
 * Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 */

`include "axi/typedef.svh"

module axi_rab_top

  // Parameters {{{
  #(
    parameter int unsigned N_PORTS             =  2,
    parameter int unsigned N_L1_SLICES [3:0]   = '{0, 0, 32, 4}, // number of L1 slices per port
    parameter int unsigned N_L1_SLICES_MAX     = 0, // maximum of per-port values above
    parameter bit          EN_ACP              = 0, // enable ACP
    parameter bit          ENABLE_L2TLB [3:0]  = '{default: 0}, // enable L2 TLB per port
    parameter int unsigned N_L2_SETS           = 32,
    parameter int unsigned N_L2_SET_ENTRIES    = 32,
    parameter int unsigned N_L2_PAR_VA_RAMS    = 4,
    parameter int unsigned AXI_DATA_WIDTH      = 64,
    parameter int unsigned AXI_S_ADDR_WIDTH    = 32,
    parameter int unsigned AXI_M_ADDR_WIDTH    = 40,
    parameter int unsigned AXI_LITE_DATA_WIDTH = 64,
    parameter int unsigned AXI_LITE_ADDR_WIDTH = 32,
    parameter int unsigned AXI_ID_WIDTH        = 10,
    parameter int unsigned AXI_USER_WIDTH      =  6,
    parameter int unsigned MH_FIFO_DEPTH       = 16,
    localparam type        axi_addr_slv_t      = logic [AXI_S_ADDR_WIDTH-1:0],
    localparam type        axi_addr_mst_t      = logic [AXI_M_ADDR_WIDTH-1:0],
    localparam type        axi_data_t          = logic [AXI_DATA_WIDTH-1:0],
    localparam type        axi_id_t            = logic [AXI_ID_WIDTH-1:0],
    localparam type        axi_strb_t          = logic [AXI_DATA_WIDTH/8-1:0],
    localparam type        axi_user_t          = logic [AXI_USER_WIDTH-1:0]
  )
  // }}}

  // Ports {{{
  (

    input logic                                            Clk_CI,  // This clock may be gated.
    input logic                                            NonGatedClk_CI,
    input logic                                            Rst_RBI,

    // For every slave port there are two master ports. The master
    // port to use can be set using the master_select flag of the protection
    // bits of a slice

    // AXI4 Slave {{{
    input  axi_id_t           [N_PORTS-1:0] s_axi4_awid,
    input  axi_addr_slv_t     [N_PORTS-1:0] s_axi4_awaddr,
    input  logic              [N_PORTS-1:0] s_axi4_awvalid,
    output logic              [N_PORTS-1:0] s_axi4_awready,
    input  axi_pkg::len_t     [N_PORTS-1:0] s_axi4_awlen,
    input  axi_pkg::size_t    [N_PORTS-1:0] s_axi4_awsize,
    input  axi_pkg::burst_t   [N_PORTS-1:0] s_axi4_awburst,
    input  logic              [N_PORTS-1:0] s_axi4_awlock,
    input  axi_pkg::prot_t    [N_PORTS-1:0] s_axi4_awprot,
    input  axi_pkg::atop_t    [N_PORTS-1:0] s_axi4_awatop,
    input  axi_pkg::cache_t   [N_PORTS-1:0] s_axi4_awcache,
    input  axi_pkg::region_t  [N_PORTS-1:0] s_axi4_awregion,
    input  axi_pkg::qos_t     [N_PORTS-1:0] s_axi4_awqos,
    input  axi_user_t         [N_PORTS-1:0] s_axi4_awuser,

    input  axi_data_t         [N_PORTS-1:0] s_axi4_wdata,
    input  logic              [N_PORTS-1:0] s_axi4_wvalid,
    output logic              [N_PORTS-1:0] s_axi4_wready,
    input  axi_strb_t         [N_PORTS-1:0] s_axi4_wstrb,
    input  logic              [N_PORTS-1:0] s_axi4_wlast,
    input  axi_user_t         [N_PORTS-1:0] s_axi4_wuser,

    output axi_id_t           [N_PORTS-1:0] s_axi4_bid,
    output axi_pkg::resp_t    [N_PORTS-1:0] s_axi4_bresp,
    output logic              [N_PORTS-1:0] s_axi4_bvalid,
    output axi_user_t         [N_PORTS-1:0] s_axi4_buser,
    input  logic              [N_PORTS-1:0] s_axi4_bready,

    input  axi_id_t           [N_PORTS-1:0] s_axi4_arid,
    input  axi_addr_slv_t     [N_PORTS-1:0] s_axi4_araddr,
    input  logic              [N_PORTS-1:0] s_axi4_arvalid,
    output logic              [N_PORTS-1:0] s_axi4_arready,
    input  axi_pkg::len_t     [N_PORTS-1:0] s_axi4_arlen,
    input  axi_pkg::size_t    [N_PORTS-1:0] s_axi4_arsize,
    input  axi_pkg::burst_t   [N_PORTS-1:0] s_axi4_arburst,
    input  logic              [N_PORTS-1:0] s_axi4_arlock,
    input  axi_pkg::prot_t    [N_PORTS-1:0] s_axi4_arprot,
    input  axi_pkg::cache_t   [N_PORTS-1:0] s_axi4_arcache,
    input  axi_pkg::region_t  [N_PORTS-1:0] s_axi4_arregion,
    input  axi_pkg::qos_t     [N_PORTS-1:0] s_axi4_arqos,
    input  axi_user_t         [N_PORTS-1:0] s_axi4_aruser,

    output axi_id_t           [N_PORTS-1:0] s_axi4_rid,
    output axi_data_t         [N_PORTS-1:0] s_axi4_rdata,
    output axi_pkg::resp_t    [N_PORTS-1:0] s_axi4_rresp,
    output logic              [N_PORTS-1:0] s_axi4_rvalid,
    input  logic              [N_PORTS-1:0] s_axi4_rready,
    output logic              [N_PORTS-1:0] s_axi4_rlast,
    output axi_user_t         [N_PORTS-1:0] s_axi4_ruser,
    // }}}

    // AXI4 Master 0 {{{
    output axi_id_t           [N_PORTS-1:0] m0_axi4_awid,
    output axi_addr_mst_t     [N_PORTS-1:0] m0_axi4_awaddr,
    output logic              [N_PORTS-1:0] m0_axi4_awvalid,
    input  logic              [N_PORTS-1:0] m0_axi4_awready,
    output axi_pkg::len_t     [N_PORTS-1:0] m0_axi4_awlen,
    output axi_pkg::size_t    [N_PORTS-1:0] m0_axi4_awsize,
    output axi_pkg::burst_t   [N_PORTS-1:0] m0_axi4_awburst,
    output logic              [N_PORTS-1:0] m0_axi4_awlock,
    output axi_pkg::prot_t    [N_PORTS-1:0] m0_axi4_awprot,
    output axi_pkg::atop_t    [N_PORTS-1:0] m0_axi4_awatop,
    output axi_pkg::cache_t   [N_PORTS-1:0] m0_axi4_awcache,
    output axi_pkg::region_t  [N_PORTS-1:0] m0_axi4_awregion,
    output axi_pkg::qos_t     [N_PORTS-1:0] m0_axi4_awqos,
    output axi_user_t         [N_PORTS-1:0] m0_axi4_awuser,

    output axi_data_t         [N_PORTS-1:0] m0_axi4_wdata,
    output logic              [N_PORTS-1:0] m0_axi4_wvalid,
    input  logic              [N_PORTS-1:0] m0_axi4_wready,
    output axi_strb_t         [N_PORTS-1:0] m0_axi4_wstrb,
    output logic              [N_PORTS-1:0] m0_axi4_wlast,
    output axi_user_t         [N_PORTS-1:0] m0_axi4_wuser,

    input  axi_id_t           [N_PORTS-1:0] m0_axi4_bid,
    input  axi_pkg::resp_t    [N_PORTS-1:0] m0_axi4_bresp,
    input  logic              [N_PORTS-1:0] m0_axi4_bvalid,
    input  axi_user_t         [N_PORTS-1:0] m0_axi4_buser,
    output logic              [N_PORTS-1:0] m0_axi4_bready,

    output axi_id_t           [N_PORTS-1:0] m0_axi4_arid,
    output axi_addr_mst_t     [N_PORTS-1:0] m0_axi4_araddr,
    output logic              [N_PORTS-1:0] m0_axi4_arvalid,
    input  logic              [N_PORTS-1:0] m0_axi4_arready,
    output axi_pkg::len_t     [N_PORTS-1:0] m0_axi4_arlen,
    output axi_pkg::size_t    [N_PORTS-1:0] m0_axi4_arsize,
    output axi_pkg::burst_t   [N_PORTS-1:0] m0_axi4_arburst,
    output logic              [N_PORTS-1:0] m0_axi4_arlock,
    output axi_pkg::prot_t    [N_PORTS-1:0] m0_axi4_arprot,
    output axi_pkg::cache_t   [N_PORTS-1:0] m0_axi4_arcache,
    output axi_pkg::region_t  [N_PORTS-1:0] m0_axi4_arregion,
    output axi_pkg::qos_t     [N_PORTS-1:0] m0_axi4_arqos,
    output axi_user_t         [N_PORTS-1:0] m0_axi4_aruser,

    input  axi_id_t           [N_PORTS-1:0] m0_axi4_rid,
    input  axi_data_t         [N_PORTS-1:0] m0_axi4_rdata,
    input  axi_pkg::resp_t    [N_PORTS-1:0] m0_axi4_rresp,
    input  logic              [N_PORTS-1:0] m0_axi4_rvalid,
    output logic              [N_PORTS-1:0] m0_axi4_rready,
    input  logic              [N_PORTS-1:0] m0_axi4_rlast,
    input  axi_user_t         [N_PORTS-1:0] m0_axi4_ruser,
    // }}}

    // AXI4 Master 1 {{{
    output axi_id_t           [N_PORTS-1:0] m1_axi4_awid,
    output axi_addr_mst_t     [N_PORTS-1:0] m1_axi4_awaddr,
    output logic              [N_PORTS-1:0] m1_axi4_awvalid,
    input  logic              [N_PORTS-1:0] m1_axi4_awready,
    output axi_pkg::len_t     [N_PORTS-1:0] m1_axi4_awlen,
    output axi_pkg::size_t    [N_PORTS-1:0] m1_axi4_awsize,
    output axi_pkg::burst_t   [N_PORTS-1:0] m1_axi4_awburst,
    output logic              [N_PORTS-1:0] m1_axi4_awlock,
    output axi_pkg::prot_t    [N_PORTS-1:0] m1_axi4_awprot,
    output axi_pkg::atop_t    [N_PORTS-1:0] m1_axi4_awatop,
    output axi_pkg::cache_t   [N_PORTS-1:0] m1_axi4_awcache,
    output axi_pkg::region_t  [N_PORTS-1:0] m1_axi4_awregion,
    output axi_pkg::qos_t     [N_PORTS-1:0] m1_axi4_awqos,
    output axi_user_t         [N_PORTS-1:0] m1_axi4_awuser,

    output axi_data_t         [N_PORTS-1:0] m1_axi4_wdata,
    output logic              [N_PORTS-1:0] m1_axi4_wvalid,
    input  logic              [N_PORTS-1:0] m1_axi4_wready,
    output axi_strb_t         [N_PORTS-1:0] m1_axi4_wstrb,
    output logic              [N_PORTS-1:0] m1_axi4_wlast,
    output axi_user_t         [N_PORTS-1:0] m1_axi4_wuser,

    input  axi_id_t           [N_PORTS-1:0] m1_axi4_bid,
    input  axi_pkg::resp_t    [N_PORTS-1:0] m1_axi4_bresp,
    input  logic              [N_PORTS-1:0] m1_axi4_bvalid,
    input  axi_user_t         [N_PORTS-1:0] m1_axi4_buser,
    output logic              [N_PORTS-1:0] m1_axi4_bready,

    output axi_id_t           [N_PORTS-1:0] m1_axi4_arid,
    output axi_addr_mst_t     [N_PORTS-1:0] m1_axi4_araddr,
    output logic              [N_PORTS-1:0] m1_axi4_arvalid,
    input  logic              [N_PORTS-1:0] m1_axi4_arready,
    output axi_pkg::len_t     [N_PORTS-1:0] m1_axi4_arlen,
    output axi_pkg::size_t    [N_PORTS-1:0] m1_axi4_arsize,
    output axi_pkg::burst_t   [N_PORTS-1:0] m1_axi4_arburst,
    output logic              [N_PORTS-1:0] m1_axi4_arlock,
    output axi_pkg::prot_t    [N_PORTS-1:0] m1_axi4_arprot,
    output axi_pkg::cache_t   [N_PORTS-1:0] m1_axi4_arcache,
    output axi_pkg::region_t  [N_PORTS-1:0] m1_axi4_arregion,
    output axi_pkg::qos_t     [N_PORTS-1:0] m1_axi4_arqos,
    output axi_user_t         [N_PORTS-1:0] m1_axi4_aruser,

    input  axi_id_t           [N_PORTS-1:0] m1_axi4_rid,
    input  axi_data_t         [N_PORTS-1:0] m1_axi4_rdata,
    input  axi_pkg::resp_t    [N_PORTS-1:0] m1_axi4_rresp,
    input  logic              [N_PORTS-1:0] m1_axi4_rvalid,
    output logic              [N_PORTS-1:0] m1_axi4_rready,
    input  logic              [N_PORTS-1:0] m1_axi4_rlast,
    input  axi_user_t         [N_PORTS-1:0] m1_axi4_ruser,
    // }}}

    // AXI 4 Lite Slave (Configuration Interface) {{{
    // AXI4-Lite port to setup the rab slices
    // use this to program the configuration registers
    input  logic                 [AXI_LITE_ADDR_WIDTH-1:0] s_axi4lite_awaddr,
    input  logic                                           s_axi4lite_awvalid,
    output logic                                           s_axi4lite_awready,

    input  logic                 [AXI_LITE_DATA_WIDTH-1:0] s_axi4lite_wdata,
    input  logic                                           s_axi4lite_wvalid,
    output logic                                           s_axi4lite_wready,
    input  logic               [AXI_LITE_DATA_WIDTH/8-1:0] s_axi4lite_wstrb,

    output logic                                     [1:0] s_axi4lite_bresp,
    output logic                                           s_axi4lite_bvalid,
    input  logic                                           s_axi4lite_bready,

    input  logic                 [AXI_LITE_ADDR_WIDTH-1:0] s_axi4lite_araddr,
    input  logic                                           s_axi4lite_arvalid,
    output logic                                           s_axi4lite_arready,

    output logic                 [AXI_LITE_DATA_WIDTH-1:0] s_axi4lite_rdata,
    output logic                                     [1:0] s_axi4lite_rresp,
    output logic                                           s_axi4lite_rvalid,
    input  logic                                           s_axi4lite_rready,
    // }}}

    // BRAMs {{{
`ifdef RAB_AX_LOG_EN
    BramPort.Slave                                         ArBram_PS,
    BramPort.Slave                                         AwBram_PS,
`endif
    // }}}

    // Logger Control {{{
`ifdef RAB_AX_LOG_EN
    input  logic                                           LogEn_SI,
    input  logic                                           ArLogClr_SI,
    input  logic                                           AwLogClr_SI,
    output logic                                           ArLogRdy_SO,
    output logic                                           AwLogRdy_SO,
`endif
    // }}}

    // Interrupt Outputs {{{
    // Interrupt lines to handle misses, collisions of slices/multiple hits,
    // protection faults and overflow of the miss handling fifo
`ifdef RAB_AX_LOG_EN
    output logic                                           int_ar_log_full,
    output logic                                           int_aw_log_full,
`endif
    output logic                             [N_PORTS-1:0] int_miss,
    output logic                             [N_PORTS-1:0] int_multi,
    output logic                             [N_PORTS-1:0] int_prot,
    output logic                                           int_mhf_full
    // }}}

  );

  // }}}

  // Signals {{{
  // ███████╗██╗ ██████╗ ███╗   ██╗ █████╗ ██╗     ███████╗
  // ██╔════╝██║██╔════╝ ████╗  ██║██╔══██╗██║     ██╔════╝
  // ███████╗██║██║  ███╗██╔██╗ ██║███████║██║     ███████╗
  // ╚════██║██║██║   ██║██║╚██╗██║██╔══██║██║     ╚════██║
  // ███████║██║╚██████╔╝██║ ╚████║██║  ██║███████╗███████║
  // ╚══════╝╚═╝ ╚═════╝ ╚═╝  ╚═══╝╚═╝  ╚═╝╚══════╝╚══════╝
  //

  // Internal AXI4 lines, these connect buffers on the slave side to the rab core and
  // multiplexers which switch between the two master outputs
  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_awid;
  logic [N_PORTS-1:0]  [AXI_S_ADDR_WIDTH-1:0] int_awaddr;
  logic [N_PORTS-1:0]                         int_awvalid;
  logic [N_PORTS-1:0]                         int_awready;
  logic [N_PORTS-1:0]                   [7:0] int_awlen;
  logic [N_PORTS-1:0]                   [2:0] int_awsize;
  logic [N_PORTS-1:0]                   [1:0] int_awburst;
  logic [N_PORTS-1:0]                         int_awlock;
  logic [N_PORTS-1:0]                   [2:0] int_awprot;
  logic [N_PORTS-1:0]                   [5:0] int_awatop;
  logic [N_PORTS-1:0]                   [3:0] int_awcache;
  logic [N_PORTS-1:0]                   [3:0] int_awregion;
  logic [N_PORTS-1:0]                   [3:0] int_awqos;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_awuser;

  logic [N_PORTS-1:0]    [AXI_DATA_WIDTH-1:0] int_wdata;
  logic [N_PORTS-1:0]                         int_wvalid;
  logic [N_PORTS-1:0]                         int_wready;
  logic [N_PORTS-1:0]  [AXI_DATA_WIDTH/8-1:0] int_wstrb;
  logic [N_PORTS-1:0]                         int_wlast;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_wuser;

  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_bid;
  logic [N_PORTS-1:0]                   [1:0] int_bresp;
  logic [N_PORTS-1:0]                         int_bvalid;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_buser;
  logic [N_PORTS-1:0]                         int_bready;

  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_arid;
  logic [N_PORTS-1:0]  [AXI_S_ADDR_WIDTH-1:0] int_araddr;
  logic [N_PORTS-1:0]                         int_arvalid;
  logic [N_PORTS-1:0]                         int_arready;
  logic [N_PORTS-1:0]                   [7:0] int_arlen;
  logic [N_PORTS-1:0]                   [2:0] int_arsize;
  logic [N_PORTS-1:0]                   [1:0] int_arburst;
  logic [N_PORTS-1:0]                         int_arlock;
  logic [N_PORTS-1:0]                   [2:0] int_arprot;
  logic [N_PORTS-1:0]                   [3:0] int_arcache;
  logic [N_PORTS-1:0]                   [3:0] int_arregion;
  logic [N_PORTS-1:0]                   [3:0] int_arqos;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_aruser;

  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_rid;
  logic [N_PORTS-1:0]                   [1:0] int_rresp;
  logic [N_PORTS-1:0]    [AXI_DATA_WIDTH-1:0] int_rdata;
  logic [N_PORTS-1:0]                         int_rlast;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_ruser;
  logic [N_PORTS-1:0]                         int_rvalid;
  logic [N_PORTS-1:0]                         int_rready;

  // rab_core outputs
  logic [N_PORTS-1:0]  [AXI_M_ADDR_WIDTH-1:0] int_wtrans_addr;
  logic [N_PORTS-1:0]                         int_wtrans_accept;
  logic [N_PORTS-1:0]                         int_wtrans_drop;
  logic [N_PORTS-1:0]                         int_wtrans_miss;
  logic [N_PORTS-1:0]                         int_wtrans_sent;
  logic [N_PORTS-1:0]                         int_wtrans_cache_coherent;
  logic [N_PORTS-1:0]                         int_wmaster_select;

  logic [N_PORTS-1:0]  [AXI_M_ADDR_WIDTH-1:0] int_rtrans_addr;
  logic [N_PORTS-1:0]                         int_rtrans_accept;
  logic [N_PORTS-1:0]                         int_rtrans_drop;
  logic [N_PORTS-1:0]                         int_rtrans_miss;
  logic [N_PORTS-1:0]                         int_rtrans_sent;
  logic [N_PORTS-1:0]                         int_rtrans_cache_coherent;
  logic [N_PORTS-1:0]                         int_rmaster_select;

  logic [N_PORTS-1:0]                         w_master_select;

  // Internal master0 AXI4 lines. These connect the first master port to the
  // multiplexers
  // For channels read address, write address and write data the other lines
  // are ignored if valid is not set, therefore we only need to multiplex those
  logic [N_PORTS-1:0]                         int_m0_awvalid;
  logic [N_PORTS-1:0]                         int_m0_awready;

  logic [N_PORTS-1:0]                         int_m0_wvalid;
  logic [N_PORTS-1:0]                         int_m0_wready;

  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_m0_bid;
  logic [N_PORTS-1:0]                   [1:0] int_m0_bresp;
  logic [N_PORTS-1:0]                         int_m0_bvalid;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_m0_buser;
  logic [N_PORTS-1:0]                         int_m0_bready;

  logic [N_PORTS-1:0]                         int_m0_arvalid;
  logic [N_PORTS-1:0]                         int_m0_arready;

  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_m0_rid;
  logic [N_PORTS-1:0]                   [1:0] int_m0_rresp;
  logic [N_PORTS-1:0]    [AXI_DATA_WIDTH-1:0] int_m0_rdata;
  logic [N_PORTS-1:0]                         int_m0_rlast;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_m0_ruser;
  logic [N_PORTS-1:0]                         int_m0_rready;
  logic [N_PORTS-1:0]                         int_m0_rvalid;

  logic [N_PORTS-1:0]                         l1_m0_ar_accept;
  logic [N_PORTS-1:0]                         l1_m0_ar_drop;
  logic [N_PORTS-1:0]                         l1_m0_ar_save;
  logic [N_PORTS-1:0]                         l1_m0_ar_done;
  logic [N_PORTS-1:0]                         l2_m0_ar_accept;
  logic [N_PORTS-1:0]                         l2_m0_ar_drop;
  logic [N_PORTS-1:0]                         l2_m0_ar_done;
  logic [N_PORTS-1:0]                         l2_m0_ar_sending;

  logic [N_PORTS-1:0]                         l1_m0_aw_accept;
  logic [N_PORTS-1:0]                         l1_m0_aw_drop;
  logic [N_PORTS-1:0]                         l1_m0_aw_save;
  logic [N_PORTS-1:0]                         l1_m0_aw_done;
  logic [N_PORTS-1:0]                         l2_m0_aw_accept;
  logic [N_PORTS-1:0]                         l2_m0_aw_drop;
  logic [N_PORTS-1:0]                         l2_m0_aw_done;
  logic [N_PORTS-1:0]                         l2_m0_aw_sending;

  // Internal master1 AXI4 lines. These connect the second master port to the
  // multiplexers
  // For channels read address, write address and write data the other lines
  // are ignored if valid is not set, therefore we only need to multiplex those
  logic [N_PORTS-1:0]                         int_m1_awvalid;
  logic [N_PORTS-1:0]                         int_m1_awready;

  logic [N_PORTS-1:0]                         int_m1_wvalid;
  logic [N_PORTS-1:0]                         int_m1_wready;

  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_m1_bid;
  logic [N_PORTS-1:0]                   [1:0] int_m1_bresp;
  logic [N_PORTS-1:0]                         int_m1_bvalid;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_m1_buser;
  logic [N_PORTS-1:0]                         int_m1_bready;

  logic [N_PORTS-1:0]                         int_m1_arvalid;
  logic [N_PORTS-1:0]                         int_m1_arready;

  logic [N_PORTS-1:0]      [AXI_ID_WIDTH-1:0] int_m1_rid;
  logic [N_PORTS-1:0]                   [1:0] int_m1_rresp;
  logic [N_PORTS-1:0]    [AXI_DATA_WIDTH-1:0] int_m1_rdata;
  logic [N_PORTS-1:0]                         int_m1_rlast;
  logic [N_PORTS-1:0]    [AXI_USER_WIDTH-1:0] int_m1_ruser;
  logic [N_PORTS-1:0]                         int_m1_rvalid;
  logic [N_PORTS-1:0]                         int_m1_rready;

  logic [N_PORTS-1:0]                         l1_m1_ar_accept;
  logic [N_PORTS-1:0]                         l1_m1_ar_drop;
  logic [N_PORTS-1:0]                         l1_m1_ar_save;
  logic [N_PORTS-1:0]                         l1_m1_ar_done;
  logic [N_PORTS-1:0]                         l2_m1_ar_accept;
  logic [N_PORTS-1:0]                         l2_m1_ar_drop;
  logic [N_PORTS-1:0]                         l2_m1_ar_done;

  logic [N_PORTS-1:0]                         l1_m1_aw_accept;
  logic [N_PORTS-1:0]                         l1_m1_aw_drop;
  logic [N_PORTS-1:0]                         l1_m1_aw_save;
  logic [N_PORTS-1:0]                         l1_m1_aw_done;
  logic [N_PORTS-1:0]                         l2_m1_aw_accept;
  logic [N_PORTS-1:0]                         l2_m1_aw_drop;
  logic [N_PORTS-1:0]                         l2_m1_aw_done;

  // L1 outputs
  logic [N_PORTS-1:0]                         rab_miss; // L1 RAB miss
  logic [N_PORTS-1:0]                         rab_prot;
  logic [N_PORTS-1:0]                         rab_multi;
  logic [N_PORTS-1:0]                         rab_prefetch;
  logic [N_PORTS-1:0]                         rab_invalidate;

  //
  // Signals used to support L2 TLB
  //
  // L2 RAM configuration signals
  logic [N_PORTS-1:0] [AXI_LITE_DATA_WIDTH-1:0] L2CfgWData_D;
  logic [N_PORTS-1:0] [AXI_LITE_ADDR_WIDTH-1:0] L2CfgWAddr_D;
  logic [N_PORTS-1:0]                           L2CfgWE_S;

  // L1 output and drop Buffer
  logic [N_PORTS-1:0]                           L1OutRwType_D, L1DropRwType_DP;
  logic [N_PORTS-1:0]      [AXI_USER_WIDTH-1:0] L1OutUser_D, L1DropUser_DP;
  logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] L1OutId_D, L1DropId_DP;
  logic [N_PORTS-1:0]                     [7:0] L1OutLen_D, L1DropLen_DP;
  logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] L1OutMinAddr_D, L1OutMaxAddr_D, L1DropAddr_DP;
  logic [N_PORTS-1:0]                           L1OutProt_D, L1DropProt_DP;
  logic [N_PORTS-1:0]                           L1OutMulti_D, L1DropMulti_DP;
  logic [N_PORTS-1:0]                           L1DropEn_S;
  logic [N_PORTS-1:0]                           L1DropPrefetch_S;

  logic [N_PORTS-1:0]                           L1DropValid_SN, L1DropValid_SP;

  // L2 input Buffer
  logic [N_PORTS-1:0]                           L2InRwType_DP;
  logic [N_PORTS-1:0]      [AXI_USER_WIDTH-1:0] L2InUser_DP;
  logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] L2InId_DP;
  logic [N_PORTS-1:0]                     [7:0] L2InLen_DP;
  logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] L2InMinAddr_DP, L2InMaxAddr_DP;
  logic [N_PORTS-1:0]                           L2InInvalidate_DP;
  logic [N_PORTS-1:0]                           L2InEn_S;

  // L2 output Buffer
  logic [N_PORTS-1:0]                           L2OutRwType_DP;
  logic [N_PORTS-1:0]      [AXI_USER_WIDTH-1:0] L2OutUser_DP;
  logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] L2OutId_DP;
  logic [N_PORTS-1:0]                     [7:0] L2OutLen_DP;
  logic [N_PORTS-1:0]    [AXI_S_ADDR_WIDTH-1:0] L2OutInAddr_DP;
  logic [N_PORTS-1:0]                           L2OutInvalidate_DP;

  logic [N_PORTS-1:0]                           L2OutHit_SN, L2OutHit_SP;
  logic [N_PORTS-1:0]                           L2OutMiss_SN, L2OutMiss_SP;
  logic [N_PORTS-1:0]                           L2OutProt_SN, L2OutProt_SP;
  logic [N_PORTS-1:0]                           L2OutMulti_SN, L2OutMulti_SP;
  logic [N_PORTS-1:0]                           L2OutCC_SN, L2OutCC_SP;
  logic [N_PORTS-1:0]    [AXI_M_ADDR_WIDTH-1:0] L2OutAddr_DN, L2OutAddr_DP;

  logic [N_PORTS-1:0]                           L2OutValid_SN, L2OutValid_SP;
  logic [N_PORTS-1:0]                           L2OutPrefetch_S;
  logic [N_PORTS-1:0]                           L2OutReady_S;
  logic [N_PORTS-1:0]                           L2OutEn_S;

   // L2 outputs
  logic [N_PORTS-1:0]                           L2Busy_S;
  logic [N_PORTS-1:0]                           L2OutValid_S;

  logic [N_PORTS-1:0]                           L2Miss_S;

  // Signals for interfacing the AXI modules
  logic [N_PORTS-1:0]                           l1_ar_accept;
  logic [N_PORTS-1:0]                           l1_aw_accept;
  logic [N_PORTS-1:0]                           l1_w_accept;
  logic [N_PORTS-1:0]                           l1_xw_accept;

  logic [N_PORTS-1:0]                           l1_ar_drop;
  logic [N_PORTS-1:0]                           l1_aw_drop;
  logic [N_PORTS-1:0]                           l1_w_drop;
  logic [N_PORTS-1:0]                           l1_xw_drop;

  logic [N_PORTS-1:0]                           l1_ar_save;
  logic [N_PORTS-1:0]                           l1_aw_save;
  logic [N_PORTS-1:0]                           l1_w_save;
  logic [N_PORTS-1:0]                           l1_xw_save;

  logic [N_PORTS-1:0]                           l1_ar_done;
  logic [N_PORTS-1:0]                           l1_r_done;
  logic [N_PORTS-1:0]                           l1_r_drop;
  logic [N_PORTS-1:0]                           lx_r_drop;
  logic [N_PORTS-1:0]                           lx_r_done;

  logic [N_PORTS-1:0]                           l1_aw_done;
  logic [N_PORTS-1:0]                           l1_w_done;
  logic [N_PORTS-1:0]                           l1_xw_done;
  logic [N_PORTS-1:0]                           l1_aw_done_SP;
  logic [N_PORTS-1:0]                           l1_w_done_SP;

  logic [N_PORTS-1:0]                           l2_ar_accept;
  logic [N_PORTS-1:0]                           l2_aw_accept;
  logic [N_PORTS-1:0]                           l2_w_accept;
  logic [N_PORTS-1:0]                           l2_xw_accept;

  logic [N_PORTS-1:0]                           l2_ar_drop;
  logic [N_PORTS-1:0]                           l2_r_drop;
  logic [N_PORTS-1:0]                           l2_xr_drop;
  logic [N_PORTS-1:0]                           l2_aw_drop;
  logic [N_PORTS-1:0]                           l2_w_drop;
  logic [N_PORTS-1:0]                           l2_xw_drop;

  logic [N_PORTS-1:0]                           l2_aw_done;
  logic [N_PORTS-1:0]                           l2_w_done;
  logic [N_PORTS-1:0]                           l2_xw_done;
  logic [N_PORTS-1:0]                           l2_aw_done_SP;
  logic [N_PORTS-1:0]                           l2_w_done_SP;

  logic [N_PORTS-1:0]                           l2_ar_done;
  logic [N_PORTS-1:0]                           l2_r_done;
  logic [N_PORTS-1:0]                           l2_xr_done;
  logic [N_PORTS-1:0]                           l2_ar_done_SP;
  logic [N_PORTS-1:0]                           l2_r_done_SP;

  logic [N_PORTS-1:0]                           l1_mx_aw_done;
  logic [N_PORTS-1:0]                           l1_mx_ar_done;
  logic [N_PORTS-1:0]                           l1_m0_aw_done_SP;
  logic [N_PORTS-1:0]                           l1_m0_ar_done_SP;
  logic [N_PORTS-1:0]                           l1_m1_aw_done_SP;
  logic [N_PORTS-1:0]                           l1_m1_ar_done_SP;

  logic [N_PORTS-1:0]                           l2_mx_aw_done;
  logic [N_PORTS-1:0]                           l2_mx_ar_done;
  logic [N_PORTS-1:0]                           l2_m0_aw_done_SP;
  logic [N_PORTS-1:0]                           l2_m0_ar_done_SP;
  logic [N_PORTS-1:0]                           l2_m1_aw_done_SP;
  logic [N_PORTS-1:0]                           l2_m1_ar_done_SP;

  logic [N_PORTS-1:0]        [AXI_ID_WIDTH-1:0] l1_id_drop, lx_id_drop, b_id_drop;
  logic [N_PORTS-1:0]                     [7:0] l1_len_drop, lx_len_drop;
  logic [N_PORTS-1:0]                           l1_prefetch_drop, lx_prefetch_drop, b_prefetch_drop;
  logic [N_PORTS-1:0]                           l1_hit_drop, lx_hit_drop, b_hit_drop;

  logic [N_PORTS-1:0]                           b_drop;
  logic [N_PORTS-1:0]                           b_done;

  logic [N_PORTS-1:0]    [AXI_M_ADDR_WIDTH-1:0] l2_aw_addr;
  logic [N_PORTS-1:0]    [AXI_M_ADDR_WIDTH-1:0] l2_ar_addr;

  logic [N_PORTS-1:0]                           l2_cache_coherent;
  logic [N_PORTS-1:0]                           l2_master_select;

  logic [N_PORTS-1:0]                           aw_in_stall;
  logic [N_PORTS-1:0]                           aw_out_stall;

  // Signals to store state of L2 invalidation
  logic [N_PORTS-1:0]                           l2_invalidate_done;
  logic [N_PORTS-1:0]                           l2_invalidate_in_progress_q, l2_invalidate_in_progress_d;

  genvar                                        i;

  // RRESP FSM
  typedef enum logic                    {IDLE, BUSY} r_resp_mux_ctrl_state_t;
  r_resp_mux_ctrl_state_t [N_PORTS-1:0] RRespMuxCtrl_SN, RRespMuxCtrl_SP;
  logic                   [N_PORTS-1:0] RRespSel_SN, RRespSel_SP;
  logic                   [N_PORTS-1:0] RRespBurst_S;
  logic                   [N_PORTS-1:0] RRespSelIm_S;

  // }}}

  // Local parameters and types {{{
  `AXI_TYPEDEF_AW_CHAN_T( axi_aw_mst_t, axi_addr_mst_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_AW_CHAN_T( axi_aw_slv_t, axi_addr_slv_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_W_CHAN_T(  axi_w_t,      axi_data_t, axi_strb_t, axi_user_t);
  `AXI_TYPEDEF_B_CHAN_T(  axi_b_t,      axi_id_t, axi_user_t);
  `AXI_TYPEDEF_AR_CHAN_T( axi_ar_mst_t, axi_addr_mst_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_AR_CHAN_T( axi_ar_slv_t, axi_addr_slv_t, axi_id_t, axi_user_t);
  `AXI_TYPEDEF_R_CHAN_T(  axi_r_t,      axi_data_t, axi_id_t, axi_user_t);

  // L2TLB parameters
  localparam integer HUM_BUFFER_DEPTH = (N_L2_SET_ENTRIES/2/N_L2_PAR_VA_RAMS)+13;

  // }}}

  // Derive `master_select` from cache coherency flag. {{{
  `ifdef EN_ACP
    assign int_wmaster_select = int_wtrans_cache_coherent;
    assign int_rmaster_select = int_rtrans_cache_coherent;
    assign l2_master_select   = l2_cache_coherent;
  `else
    assign int_wmaster_select = '0;
    assign int_rmaster_select = '0;
    assign l2_master_select   = '0;
  `endif
  // }}}

  // Buf and Send {{{
  // ██████╗ ██╗   ██╗███████╗       ██╗       ███████╗███████╗███╗   ██╗██████╗
  // ██╔══██╗██║   ██║██╔════╝       ██║       ██╔════╝██╔════╝████╗  ██║██╔══██╗
  // ██████╔╝██║   ██║█████╗      ████████╗    ███████╗█████╗  ██╔██╗ ██║██║  ██║
  // ██╔══██╗██║   ██║██╔══╝      ██╔═██╔═╝    ╚════██║██╔══╝  ██║╚██╗██║██║  ██║
  // ██████╔╝╚██████╔╝██║         ██████║      ███████║███████╗██║ ╚████║██████╔╝
  // ╚═════╝  ╚═════╝ ╚═╝         ╚═════╝      ╚══════╝╚══════╝╚═╝  ╚═══╝╚═════╝
  //
  logic[N_PORTS-1:0] m0_write_is_burst, m0_read_is_burst;
  logic[N_PORTS-1:0] m1_write_is_burst, m1_read_is_burst;

  generate for (i = 0; i < N_PORTS; i++) begin : BUF_AND_SEND

  // Write Address channel (aw) {{{
  /*
   * write address channel (aw)
   *
   * ██╗    ██╗██████╗ ██╗████████╗███████╗     █████╗ ██████╗ ██████╗ ██████╗
   * ██║    ██║██╔══██╗██║╚══██╔══╝██╔════╝    ██╔══██╗██╔══██╗██╔══██╗██╔══██╗
   * ██║ █╗ ██║██████╔╝██║   ██║   █████╗      ███████║██║  ██║██║  ██║██████╔╝
   * ██║███╗██║██╔══██╗██║   ██║   ██╔══╝      ██╔══██║██║  ██║██║  ██║██╔══██╗
   * ╚███╔███╔╝██║  ██║██║   ██║   ███████╗    ██║  ██║██████╔╝██████╔╝██║  ██║
   *  ╚══╝╚══╝ ╚═╝  ╚═╝╚═╝   ╚═╝   ╚══════╝    ╚═╝  ╚═╝╚═════╝ ╚═════╝ ╚═╝  ╚═╝
   *
   */

  axi_aw_slv_t aw_buf_oup;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (4),
    .T            (axi_aw_slv_t)
  ) i_aw_buf (
    .clk_i      (Clk_CI),
    .rst_ni     (Rst_RBI),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ id:       s_axi4_awid[i],
                    addr:     s_axi4_awaddr[i],
                    len:      s_axi4_awlen[i],
                    size:     s_axi4_awsize[i],
                    burst:    s_axi4_awburst[i],
                    lock:     s_axi4_awlock[i],
                    prot:     s_axi4_awprot[i],
                    atop:     s_axi4_awatop[i],
                    cache:    s_axi4_awcache[i],
                    region:   s_axi4_awregion[i],
                    qos:      s_axi4_awqos[i],
                    user:     s_axi4_awuser[i],
                    default:  '0}),
    .valid_i    (s_axi4_awvalid[i]),
    .ready_o    (s_axi4_awready[i]),
    .data_o     (aw_buf_oup),
    .valid_o    (int_awvalid[i]),
    .ready_i    (int_awready[i]),
    .usage_o    (/* unused */)
  );
  assign int_awid[i]      = aw_buf_oup.id;
  assign int_awaddr[i]    = aw_buf_oup.addr;
  assign int_awlen[i]     = aw_buf_oup.len;
  assign int_awsize[i]    = aw_buf_oup.size;
  assign int_awburst[i]   = aw_buf_oup.burst;
  assign int_awlock[i]    = aw_buf_oup.lock;
  assign int_awprot[i]    = aw_buf_oup.prot;
  assign int_awatop[i]    = aw_buf_oup.atop;
  assign int_awcache[i]   = aw_buf_oup.cache;
  assign int_awregion[i]  = aw_buf_oup.region;
  assign int_awqos[i]     = aw_buf_oup.qos;
  assign int_awuser[i]    = aw_buf_oup.user;

  axi4_aw_sender
    #(
      .AXI_ADDR_WIDTH ( AXI_M_ADDR_WIDTH ),
      .AXI_ID_WIDTH   ( AXI_ID_WIDTH     ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH   ),
      .ENABLE_L2TLB   ( ENABLE_L2TLB[i]  )
      )
    u_aw_sender_m0
    (
      .axi4_aclk       ( Clk_CI                ),
      .axi4_arstn      ( Rst_RBI               ),
      .l1_done_o       ( l1_m0_aw_done[i]      ),
      .l1_accept_i     ( l1_m0_aw_accept[i]    ),
      .l1_drop_i       ( l1_m0_aw_drop[i]      ),
      .l1_save_i       ( l1_m0_aw_save[i]      ),
      .l2_done_o       ( l2_m0_aw_done[i]      ),
      .l2_accept_i     ( l2_m0_aw_accept[i]    ),
      .l2_drop_i       ( l2_m0_aw_drop[i]      ),
      .l2_sending_o    ( l2_m0_aw_sending[i]   ),
      .l1_awaddr_i     ( int_wtrans_addr[i]    ),
      .l2_awaddr_i     ( l2_aw_addr[i]         ),
      .s_axi4_awid     ( int_awid[i]           ),
      .s_axi4_awvalid  ( int_m0_awvalid[i]     ),
      .s_axi4_awready  ( int_m0_awready[i]     ),
      .s_axi4_awlen    ( int_awlen[i]          ),
      .s_axi4_awsize   ( int_awsize[i]         ),
      .s_axi4_awburst  ( int_awburst[i]        ),
      .s_axi4_awlock   ( int_awlock[i]         ),
      .s_axi4_awprot   ( int_awprot[i]         ),
      .s_axi4_awatop   ( int_awatop[i]         ),
      .s_axi4_awcache  ( int_awcache[i]        ),
      .s_axi4_awregion ( int_awregion[i]       ),
      .s_axi4_awqos    ( int_awqos[i]          ),
      .s_axi4_awuser   ( int_awuser[i]         ),
      .m_axi4_awid     ( m0_axi4_awid[i]       ),
      .m_axi4_awaddr   ( m0_axi4_awaddr[i]     ),
      .m_axi4_awvalid  ( m0_axi4_awvalid[i]    ),
      .m_axi4_awready  ( m0_axi4_awready[i]    ),
      .m_axi4_awlen    ( m0_axi4_awlen[i]      ),
      .m_axi4_awsize   ( m0_axi4_awsize[i]     ),
      .m_axi4_awburst  ( m0_axi4_awburst[i]    ),
      .m_axi4_awlock   ( m0_axi4_awlock[i]     ),
      .m_axi4_awprot   ( m0_axi4_awprot[i]     ),
      .m_axi4_awatop   ( m0_axi4_awatop[i]     ),
      .m_axi4_awcache  (                       ),
      .m_axi4_awregion ( m0_axi4_awregion[i]   ),
      .m_axi4_awqos    ( m0_axi4_awqos[i]      ),
      .m_axi4_awuser   ( m0_axi4_awuser[i]     )
    );

  // The AXCACHE signals are set according to burstiness and cache coherence or statically
  // when not connected to ACP on Zynq (implemented below).
    assign m0_write_is_burst[i] = (m0_axi4_awlen[i] != {8{1'b0}}) && (m0_axi4_awburst[i] != 2'b00);
  `ifndef EN_ACP
    always_comb begin
      if ( (l2_m0_aw_sending[i] & l2_cache_coherent[i]) | int_wtrans_cache_coherent[i]) begin
        if (m0_write_is_burst[i]) begin
          m0_axi4_awcache[i]  = 4'b0111;
        end else begin
          m0_axi4_awcache[i]  = 4'b1111;
        end
      end else begin
        m0_axi4_awcache[i]    = 4'b0011;
      end
    end
  `else
    assign m0_axi4_awcache[i] = 4'b0011;
  `endif

  axi4_aw_sender
    #(
      .AXI_ADDR_WIDTH ( AXI_M_ADDR_WIDTH ),
      .AXI_ID_WIDTH   ( AXI_ID_WIDTH     ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH   ),
      .ENABLE_L2TLB   ( ENABLE_L2TLB[i]  )
      )
    u_aw_sender_m1
    (
      .axi4_aclk       ( Clk_CI                ),
      .axi4_arstn      ( Rst_RBI               ),
      .l1_accept_i     ( l1_m1_aw_accept[i]    ),
      .l1_drop_i       ( l1_m1_aw_drop[i]      ),
      .l1_save_i       ( l1_m1_aw_save[i]      ),
      .l1_done_o       ( l1_m1_aw_done[i]      ),
      .l2_accept_i     ( l2_m1_aw_accept[i]    ),
      .l2_drop_i       ( l2_m1_aw_drop[i]      ),
      .l2_done_o       ( l2_m1_aw_done[i]      ),
      .l2_sending_o    (                       ), // just helps to set axcache
      .l1_awaddr_i     ( int_wtrans_addr[i]    ),
      .l2_awaddr_i     ( l2_aw_addr[i]         ),
      .s_axi4_awid     ( int_awid[i]           ),
      .s_axi4_awvalid  ( int_m1_awvalid[i]     ),
      .s_axi4_awready  ( int_m1_awready[i]     ),
      .s_axi4_awlen    ( int_awlen[i]          ),
      .s_axi4_awsize   ( int_awsize[i]         ),
      .s_axi4_awburst  ( int_awburst[i]        ),
      .s_axi4_awlock   ( int_awlock[i]         ),
      .s_axi4_awprot   ( int_awprot[i]         ),
      .s_axi4_awatop   ( int_awatop[i]         ),
      .s_axi4_awcache  ( int_awcache[i]        ),
      .s_axi4_awregion ( int_awregion[i]       ),
      .s_axi4_awqos    ( int_awqos[i]          ),
      .s_axi4_awuser   ( int_awuser[i]         ),
      .m_axi4_awid     ( m1_axi4_awid[i]       ),
      .m_axi4_awaddr   ( m1_axi4_awaddr[i]     ),
      .m_axi4_awvalid  ( m1_axi4_awvalid[i]    ),
      .m_axi4_awready  ( m1_axi4_awready[i]    ),
      .m_axi4_awlen    ( m1_axi4_awlen[i]      ),
      .m_axi4_awsize   ( m1_axi4_awsize[i]     ),
      .m_axi4_awburst  ( m1_axi4_awburst[i]    ),
      .m_axi4_awlock   ( m1_axi4_awlock[i]     ),
      .m_axi4_awprot   ( m1_axi4_awprot[i]     ),
      .m_axi4_awatop   ( m1_axi4_awatop[i]     ),
      .m_axi4_awcache  (                       ),
      .m_axi4_awregion ( m1_axi4_awregion[i]   ),
      .m_axi4_awqos    ( m1_axi4_awqos[i]      ),
      .m_axi4_awuser   ( m1_axi4_awuser[i]     )
    );

    // The AXCACHE signals are set according to burstiness and cache coherence or statically
    // when not connected to ACP on Zynq (implemented below).
      assign m1_write_is_burst[i] = (m1_axi4_awlen[i] != {8{1'b0}}) && (m1_axi4_awburst[i] != 2'b00);
    `ifdef EN_ACP
      always_comb begin
        if (m1_write_is_burst[i]) begin
          m1_axi4_awcache[i]    = 4'b1011;
        end else begin
          m1_axi4_awcache[i]    = 4'b1111;
        end
      end
    `else
      assign m1_axi4_awcache[i] = 4'b0011;
    `endif

  // }}}

  // Write Data channel (w) {{{
  /*
   * write data channel (w)
   *
   * ██╗    ██╗██████╗ ██╗████████╗███████╗    ██████╗  █████╗ ████████╗ █████╗
   * ██║    ██║██╔══██╗██║╚══██╔══╝██╔════╝    ██╔══██╗██╔══██╗╚══██╔══╝██╔══██╗
   * ██║ █╗ ██║██████╔╝██║   ██║   █████╗      ██║  ██║███████║   ██║   ███████║
   * ██║███╗██║██╔══██╗██║   ██║   ██╔══╝      ██║  ██║██╔══██║   ██║   ██╔══██║
   * ╚███╔███╔╝██║  ██║██║   ██║   ███████╗    ██████╔╝██║  ██║   ██║   ██║  ██║
   *  ╚══╝╚══╝ ╚═╝  ╚═╝╚═╝   ╚═╝   ╚══════╝    ╚═════╝ ╚═╝  ╚═╝   ╚═╝   ╚═╝  ╚═╝
   *
   */
  axi4_w_buffer
    #(
      .AXI_DATA_WIDTH   ( AXI_DATA_WIDTH   ),
      .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
      .AXI_USER_WIDTH   ( AXI_USER_WIDTH   ),
      .ENABLE_L2TLB     ( ENABLE_L2TLB[i]  ),
      .HUM_BUFFER_DEPTH ( HUM_BUFFER_DEPTH )
      )
    u_w_buffer
    (
      .axi4_aclk       ( Clk_CI                ),
      .axi4_arstn      ( Rst_RBI               ),

      // L1 interface
      .l1_done_o       ( l1_w_done[i]          ),
      .l1_accept_i     ( l1_w_accept[i]        ),
      .l1_save_i       ( l1_w_save[i]          ),
      .l1_drop_i       ( l1_w_drop[i]          ),
      .l1_master_i     ( int_wmaster_select[i] ),
      .l1_id_i         ( l1_id_drop[i]         ),
      .l1_len_i        ( l1_len_drop[i]        ),
      .l1_prefetch_i   ( l1_prefetch_drop[i]   ),
      .l1_hit_i        ( l1_hit_drop[i]        ),

      // L2 interface
      .l2_done_o       ( l2_w_done[i]          ),
      .l2_accept_i     ( l2_w_accept[i]        ),
      .l2_drop_i       ( l2_w_drop[i]          ),
      .l2_master_i     ( l2_master_select[i]   ),
      .l2_id_i         ( lx_id_drop[i]         ),
      .l2_len_i        ( lx_len_drop[i]        ),
      .l2_prefetch_i   ( lx_prefetch_drop[i]   ),
      .l2_hit_i        ( lx_hit_drop[i]        ),

      // Top-level control outputs
      .master_select_o ( w_master_select[i]    ),
      .input_stall_o   ( aw_in_stall[i]        ), // stall L1 AW input if request buffers full
      .output_stall_o  ( aw_out_stall[i]       ), // stall L1 AW hit forwarding if bypass not possible

      // B sender interface
      .b_drop_o        ( b_drop[i]             ),
      .b_done_i        ( b_done[i]             ),
      .id_o            ( b_id_drop[i]          ),
      .prefetch_o      ( b_prefetch_drop[i]    ),
      .hit_o           ( b_hit_drop[i]         ),

      // AXI W channel interfaces
      .s_axi4_wdata    ( s_axi4_wdata[i]       ),
      .s_axi4_wvalid   ( s_axi4_wvalid[i]      ),
      .s_axi4_wready   ( s_axi4_wready[i]      ),
      .s_axi4_wstrb    ( s_axi4_wstrb[i]       ),
      .s_axi4_wlast    ( s_axi4_wlast[i]       ),
      .s_axi4_wuser    ( s_axi4_wuser[i]       ),
      .m_axi4_wdata    ( int_wdata[i]          ),
      .m_axi4_wvalid   ( int_wvalid[i]         ),
      .m_axi4_wready   ( int_wready[i]         ),
      .m_axi4_wstrb    ( int_wstrb[i]          ),
      .m_axi4_wlast    ( int_wlast[i]          ),
      .m_axi4_wuser    ( int_wuser[i]          )
    );

  axi4_w_sender
    #(
      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH )
      )
    u_w_sender_m0
    (
      .axi4_aclk       ( Clk_CI            ),
      .axi4_arstn      ( Rst_RBI           ),
      .s_axi4_wdata    ( int_wdata[i]      ),
      .s_axi4_wvalid   ( int_m0_wvalid[i]  ),
      .s_axi4_wready   ( int_m0_wready[i]  ),
      .s_axi4_wstrb    ( int_wstrb[i]      ),
      .s_axi4_wlast    ( int_wlast[i]      ),
      .s_axi4_wuser    ( int_wuser[i]      ),
      .m_axi4_wdata    ( m0_axi4_wdata[i]  ),
      .m_axi4_wvalid   ( m0_axi4_wvalid[i] ),
      .m_axi4_wready   ( m0_axi4_wready[i] ),
      .m_axi4_wstrb    ( m0_axi4_wstrb[i]  ),
      .m_axi4_wlast    ( m0_axi4_wlast[i]  ),
      .m_axi4_wuser    ( m0_axi4_wuser[i]  )
    );

  axi4_w_sender
    #(
      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH )

      )
    u_w_sender_m1
    (
      .axi4_aclk       ( Clk_CI            ),
      .axi4_arstn      ( Rst_RBI           ),
      .s_axi4_wdata    ( int_wdata[i]      ),
      .s_axi4_wvalid   ( int_m1_wvalid[i]  ),
      .s_axi4_wready   ( int_m1_wready[i]  ),
      .s_axi4_wstrb    ( int_wstrb[i]      ),
      .s_axi4_wlast    ( int_wlast[i]      ),
      .s_axi4_wuser    ( int_wuser[i]      ),
      .m_axi4_wdata    ( m1_axi4_wdata[i]  ),
      .m_axi4_wvalid   ( m1_axi4_wvalid[i] ),
      .m_axi4_wready   ( m1_axi4_wready[i] ),
      .m_axi4_wstrb    ( m1_axi4_wstrb[i]  ),
      .m_axi4_wlast    ( m1_axi4_wlast[i]  ),
      .m_axi4_wuser    ( m1_axi4_wuser[i]  )
    );

  /*
   * Multiplexer to switch between the two output master ports on the write data (w) channel
   */
  always_comb begin
    /* Only one output can be selected at any time */
    if (w_master_select[i] == 1'b0) begin
      int_m0_wvalid[i] = int_wvalid[i];
      int_m1_wvalid[i] = 1'b0;
      int_wready[i]    = int_m0_wready[i];
    end else begin
      int_m0_wvalid[i] = 1'b0;
      int_m1_wvalid[i] = int_wvalid[i];
      int_wready[i]    = int_m1_wready[i];
    end
  end

  // }}}

  // Write Response channel (b) {{{
  /*
   * write response channel (b)
   *
   * ██╗    ██╗██████╗ ██╗████████╗███████╗    ██████╗ ███████╗███████╗██████╗
   * ██║    ██║██╔══██╗██║╚══██╔══╝██╔════╝    ██╔══██╗██╔════╝██╔════╝██╔══██╗
   * ██║ █╗ ██║██████╔╝██║   ██║   █████╗      ██████╔╝█████╗  ███████╗██████╔╝
   * ██║███╗██║██╔══██╗██║   ██║   ██╔══╝      ██╔══██╗██╔══╝  ╚════██║██╔═══╝
   * ╚███╔███╔╝██║  ██║██║   ██║   ███████╗    ██║  ██║███████╗███████║██║
   *  ╚══╝╚══╝ ╚═╝  ╚═╝╚═╝   ╚═╝   ╚══════╝    ╚═╝  ╚═╝╚══════╝╚══════╝╚═╝
   *
   */
  axi_b_t b_buf_m0_oup;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (4),
    .T            (axi_b_t)
  ) i_b_buf_m0 (
    .clk_i      (Clk_CI),
    .rst_ni     (Rst_RBI),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ id:       m0_axi4_bid[i],
                    resp:     m0_axi4_bresp[i],
                    user:     m0_axi4_buser[i],
                    default:  '0}),
    .valid_i    (m0_axi4_bvalid[i]),
    .ready_o    (m0_axi4_bready[i]),
    .data_o     (b_buf_m0_oup),
    .valid_o    (int_m0_bvalid[i]),
    .ready_i    (int_m0_bready[i]),
    .usage_o    (/* unused */)
  );
  assign int_m0_bid[i]   = b_buf_m0_oup.id;
  assign int_m0_bresp[i] = b_buf_m0_oup.resp;
  assign int_m0_buser[i] = b_buf_m0_oup.user;

  axi_b_t b_buf_m1_oup;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (4),
    .T            (axi_b_t)
  ) i_b_buf_m1 (
    .clk_i      (Clk_CI),
    .rst_ni     (Rst_RBI),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ id:       m1_axi4_bid[i],
                    resp:     m1_axi4_bresp[i],
                    user:     m1_axi4_buser[i],
                    default:  '0}),
    .valid_i    (m1_axi4_bvalid[i]),
    .ready_o    (m1_axi4_bready[i]),
    .data_o     (b_buf_m1_oup),
    .valid_o    (int_m1_bvalid[i]),
    .ready_i    (int_m1_bready[i]),
    .usage_o    (/* unused */)
  );
  assign int_m1_bid[i]   = b_buf_m1_oup.id;
  assign int_m1_bresp[i] = b_buf_m1_oup.resp;
  assign int_m1_buser[i] = b_buf_m1_oup.user;

  axi4_b_sender
    #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH  )
      )
    u_b_sender
    (
      .axi4_aclk      ( Clk_CI             ),
      .axi4_arstn     ( Rst_RBI            ),
      .drop_i         ( b_drop[i]          ),
      .done_o         ( b_done[i]          ),
      .id_i           ( b_id_drop[i]       ),
      .prefetch_i     ( b_prefetch_drop[i] ),
      .hit_i          ( b_hit_drop[i]      ),
      .s_axi4_bid     ( s_axi4_bid[i]      ),
      .s_axi4_bresp   ( s_axi4_bresp[i]    ),
      .s_axi4_bvalid  ( s_axi4_bvalid[i]   ),
      .s_axi4_buser   ( s_axi4_buser[i]    ),
      .s_axi4_bready  ( s_axi4_bready[i]   ),
      .m_axi4_bid     ( int_bid[i]         ),
      .m_axi4_bresp   ( int_bresp[i]       ),
      .m_axi4_bvalid  ( int_bvalid[i]      ),
      .m_axi4_buser   ( int_buser[i]       ),
      .m_axi4_bready  ( int_bready[i]      )
    );

  /*
   * Multiplexer to switch between the two output master ports on the write response (b) channel
   */
  always_comb begin
     /* Output 1 always gets priority, so if it has something to send connect
      it and let output 0 wait using rready = 0 */
    if (int_m1_bvalid[i] == 1'b1) begin
      int_m0_bready[i] = 1'b0;
      int_m1_bready[i] = int_bready[i];

      int_bid[i]       = int_m1_bid[i];
      int_bresp[i]     = int_m1_bresp[i];
      int_buser[i]     = int_m1_buser[i];
      int_bvalid[i]    = int_m1_bvalid[i];
    end else begin
      int_m0_bready[i] = int_bready[i];
      int_m1_bready[i] = 1'b0;

      int_bid[i]       = int_m0_bid[i];
      int_bresp[i]     = int_m0_bresp[i];
      int_buser[i]     = int_m0_buser[i];
      int_bvalid[i]    = int_m0_bvalid[i];
    end
  end

  // }}}

  // Read Address channel (ar) {{{
  /*
   * read address channel (ar)
   *
   * ██████╗ ███████╗ █████╗ ██████╗      █████╗ ██████╗ ██████╗ ██████╗
   * ██╔══██╗██╔════╝██╔══██╗██╔══██╗    ██╔══██╗██╔══██╗██╔══██╗██╔══██╗
   * ██████╔╝█████╗  ███████║██║  ██║    ███████║██║  ██║██║  ██║██████╔╝
   * ██╔══██╗██╔══╝  ██╔══██║██║  ██║    ██╔══██║██║  ██║██║  ██║██╔══██╗
   * ██║  ██║███████╗██║  ██║██████╔╝    ██║  ██║██████╔╝██████╔╝██║  ██║
   * ╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝╚═════╝     ╚═╝  ╚═╝╚═════╝ ╚═════╝ ╚═╝  ╚═╝
   *
   */
  axi_ar_slv_t ar_buf_oup;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (4),
    .T            (axi_ar_slv_t)
  ) i_ar_buf (
    .clk_i      (Clk_CI),
    .rst_ni     (Rst_RBI),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ id:       s_axi4_arid[i],
                    addr:     s_axi4_araddr[i],
                    len:      s_axi4_arlen[i],
                    size:     s_axi4_arsize[i],
                    burst:    s_axi4_arburst[i],
                    lock:     s_axi4_arlock[i],
                    prot:     s_axi4_arprot[i],
                    cache:    s_axi4_arcache[i],
                    region:   s_axi4_arregion[i],
                    qos:      s_axi4_arqos[i],
                    user:     s_axi4_aruser[i],
                    default:  '0}),
    .valid_i    (s_axi4_arvalid[i]),
    .ready_o    (s_axi4_arready[i]),
    .data_o     (ar_buf_oup),
    .valid_o    (int_arvalid[i]),
    .ready_i    (int_arready[i]),
    .usage_o    (/* unused */)
  );
  assign int_arid[i]    = ar_buf_oup.id;
  assign int_araddr[i]  = ar_buf_oup.addr;
  assign int_arlen[i]   = ar_buf_oup.len;
  assign int_arsize[i]  = ar_buf_oup.size;
  assign int_arburst[i] = ar_buf_oup.burst;
  assign int_arlock[i]  = ar_buf_oup.lock;
  assign int_arprot[i]  = ar_buf_oup.prot;
  assign int_arcache[i] = ar_buf_oup.cache;
  assign int_arregion[i]= ar_buf_oup.region;
  assign int_arqos[i]   = ar_buf_oup.qos;
  assign int_aruser[i]  = ar_buf_oup.user;

  axi4_ar_sender
    #(
      .AXI_ADDR_WIDTH ( AXI_M_ADDR_WIDTH ),
      .AXI_ID_WIDTH   ( AXI_ID_WIDTH     ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH   ),
      .ENABLE_L2TLB   ( ENABLE_L2TLB[i]  )
      )
    u_ar_sender_m0
    (
      .axi4_aclk       ( Clk_CI                ),
      .axi4_arstn      ( Rst_RBI               ),
      .l1_done_o       ( l1_m0_ar_done[i]      ),
      .l1_accept_i     ( l1_m0_ar_accept[i]    ),
      .l1_drop_i       ( l1_m0_ar_drop[i]      ),
      .l1_save_i       ( l1_m0_ar_save[i]      ),
      .l2_done_o       ( l2_m0_ar_done[i]      ),
      .l2_accept_i     ( l2_m0_ar_accept[i]    ),
      .l2_drop_i       ( l2_m0_ar_drop[i]      ),
      .l2_sending_o    ( l2_m0_ar_sending[i]   ),
      .l1_araddr_i     ( int_rtrans_addr[i]    ),
      .l2_araddr_i     ( l2_ar_addr[i]         ),
      .s_axi4_arid     ( int_arid[i]           ),
      .s_axi4_arvalid  ( int_m0_arvalid[i]     ),
      .s_axi4_arready  ( int_m0_arready[i]     ),
      .s_axi4_arlen    ( int_arlen[i]          ),
      .s_axi4_arsize   ( int_arsize[i]         ),
      .s_axi4_arburst  ( int_arburst[i]        ),
      .s_axi4_arlock   ( int_arlock[i]         ),
      .s_axi4_arprot   ( int_arprot[i]         ),
      .s_axi4_arcache  ( int_arcache[i]        ),
      .s_axi4_arregion ( int_arregion[i]       ),
      .s_axi4_arqos    ( int_arqos[i]          ),
      .s_axi4_aruser   ( int_aruser[i]         ),
      .m_axi4_arid     ( m0_axi4_arid[i]       ),
      .m_axi4_araddr   ( m0_axi4_araddr[i]     ),
      .m_axi4_arvalid  ( m0_axi4_arvalid[i]    ),
      .m_axi4_arready  ( m0_axi4_arready[i]    ),
      .m_axi4_arlen    ( m0_axi4_arlen[i]      ),
      .m_axi4_arsize   ( m0_axi4_arsize[i]     ),
      .m_axi4_arburst  ( m0_axi4_arburst[i]    ),
      .m_axi4_arlock   ( m0_axi4_arlock[i]     ),
      .m_axi4_arprot   ( m0_axi4_arprot[i]     ),
      .m_axi4_arcache  (                       ),
      .m_axi4_arregion ( m0_axi4_arregion[i]   ),
      .m_axi4_arqos    ( m0_axi4_arqos[i]      ),
      .m_axi4_aruser   ( m0_axi4_aruser[i]     )
    );

    // The AXCACHE signals are set according to burstiness and cache coherence or statically
    // when not connected to ACP on Zynq (implemented below).
      assign m0_read_is_burst[i] = (m0_axi4_arlen[i] != {8{1'b0}}) && (m0_axi4_arburst[i] != 2'b00);
    `ifndef EN_ACP
      always_comb begin
        if ( (l2_m0_ar_sending[i] & l2_cache_coherent[i]) | int_rtrans_cache_coherent[i]) begin
          if (m0_read_is_burst[i]) begin
            m0_axi4_arcache[i]  = 4'b1011;
          end else begin
            m0_axi4_arcache[i]  = 4'b1111;
          end
        end else begin
          m0_axi4_arcache[i]    = 4'b0011;
        end
      end
    `else
      assign m0_axi4_arcache[i] = 4'b0011;
    `endif

  axi4_ar_sender
    #(
      .AXI_ADDR_WIDTH ( AXI_M_ADDR_WIDTH ),
      .AXI_ID_WIDTH   ( AXI_ID_WIDTH     ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH   ),
      .ENABLE_L2TLB   ( ENABLE_L2TLB[i]  )
      )
    u_ar_sender_m1
    (
      .axi4_aclk       ( Clk_CI                ),
      .axi4_arstn      ( Rst_RBI               ),
      .l1_done_o       ( l1_m1_ar_done[i]      ),
      .l1_accept_i     ( l1_m1_ar_accept[i]    ),
      .l1_drop_i       ( l1_m1_ar_drop[i]      ),
      .l1_save_i       ( l1_m1_ar_save[i]      ),
      .l2_done_o       ( l2_m1_ar_done[i]      ),
      .l2_accept_i     ( l2_m1_ar_accept[i]    ),
      .l2_drop_i       ( l2_m1_ar_drop[i]      ),
      .l2_sending_o    (                       ), // just helps to set axcache
      .l1_araddr_i     ( int_rtrans_addr[i]    ),
      .l2_araddr_i     ( l2_ar_addr[i]         ),
      .s_axi4_arid     ( int_arid[i]           ),
      .s_axi4_arvalid  ( int_m1_arvalid[i]     ),
      .s_axi4_arready  ( int_m1_arready[i]     ),
      .s_axi4_arlen    ( int_arlen[i]          ),
      .s_axi4_arsize   ( int_arsize[i]         ),
      .s_axi4_arburst  ( int_arburst[i]        ),
      .s_axi4_arlock   ( int_arlock[i]         ),
      .s_axi4_arprot   ( int_arprot[i]         ),
      .s_axi4_arcache  ( int_arcache[i]        ),
      .s_axi4_arregion ( int_arregion[i]       ),
      .s_axi4_arqos    ( int_arqos[i]          ),
      .s_axi4_aruser   ( int_aruser[i]         ),
      .m_axi4_arid     ( m1_axi4_arid[i]       ),
      .m_axi4_araddr   ( m1_axi4_araddr[i]     ),
      .m_axi4_arvalid  ( m1_axi4_arvalid[i]    ),
      .m_axi4_arready  ( m1_axi4_arready[i]    ),
      .m_axi4_arlen    ( m1_axi4_arlen[i]      ),
      .m_axi4_arsize   ( m1_axi4_arsize[i]     ),
      .m_axi4_arburst  ( m1_axi4_arburst[i]    ),
      .m_axi4_arlock   ( m1_axi4_arlock[i]     ),
      .m_axi4_arprot   ( m1_axi4_arprot[i]     ),
      .m_axi4_arcache  (                       ),
      .m_axi4_arregion ( m1_axi4_arregion[i]   ),
      .m_axi4_arqos    ( m1_axi4_arqos[i]      ),
      .m_axi4_aruser   ( m1_axi4_aruser[i]     )
    );

    // The AXCACHE signals are set according to burstiness and cache coherence or statically
    // when not connected to ACP on Zynq (implemented below).
      assign m1_read_is_burst[i] = (m1_axi4_arlen[i] != {8{1'b0}}) && (m1_axi4_arburst[i] != 2'b00);
    `ifdef EN_ACP
      always_comb begin
        if (m1_read_is_burst[i]) begin
          m1_axi4_arcache[i]    = 4'b1011;
        end else begin
          m1_axi4_arcache[i]    = 4'b1111;
        end
      end
    `else
      assign m1_axi4_arcache[i] = 4'b0011;
    `endif

  // }}}

  // Read Response channel (r) {{{
  /*
   * read response channel (r)
   *
   * ██████╗ ███████╗ █████╗ ██████╗     ██████╗ ███████╗███████╗██████╗
   * ██╔══██╗██╔════╝██╔══██╗██╔══██╗    ██╔══██╗██╔════╝██╔════╝██╔══██╗
   * ██████╔╝█████╗  ███████║██║  ██║    ██████╔╝█████╗  ███████╗██████╔╝
   * ██╔══██╗██╔══╝  ██╔══██║██║  ██║    ██╔══██╗██╔══╝  ╚════██║██╔═══╝
   * ██║  ██║███████╗██║  ██║██████╔╝    ██║  ██║███████╗███████║██║
   * ╚═╝  ╚═╝╚══════╝╚═╝  ╚═╝╚═════╝     ╚═╝  ╚═╝╚══════╝╚══════╝╚═╝
   *
   */
  axi_r_t r_buf_m0_oup;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (4),
    .T            (axi_r_t)
  ) i_r_buf_m0 (
    .clk_i      (Clk_CI),
    .rst_ni     (Rst_RBI),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ id:       m0_axi4_rid[i],
                    resp:     m0_axi4_rresp[i],
                    data:     m0_axi4_rdata[i],
                    last:     m0_axi4_rlast[i],
                    user:     m0_axi4_ruser[i],
                    default:  '0}),
    .valid_i    (m0_axi4_rvalid[i]),
    .ready_o    (m0_axi4_rready[i]),
    .data_o     (r_buf_m0_oup),
    .valid_o    (int_m0_rvalid[i]),
    .ready_i    (int_m0_rready[i]),
    .usage_o    (/* unused */)
  );
  assign int_m0_rid[i]   = r_buf_m0_oup.id;
  assign int_m0_rresp[i] = r_buf_m0_oup.resp;
  assign int_m0_rdata[i] = r_buf_m0_oup.data;
  assign int_m0_rlast[i] = r_buf_m0_oup.last;
  assign int_m0_ruser[i] = r_buf_m0_oup.user;

  axi_r_t r_buf_m1_oup;
  stream_fifo #(
    .FALL_THROUGH (1'b0),
    .DEPTH        (4),
    .T            (axi_r_t)
  ) i_r_buf_m1 (
    .clk_i      (Clk_CI),
    .rst_ni     (Rst_RBI),
    .flush_i    (1'b0),
    .testmode_i (1'b0),
    .data_i     ('{ id:       m1_axi4_rid[i],
                    resp:     m1_axi4_rresp[i],
                    data:     m1_axi4_rdata[i],
                    last:     m1_axi4_rlast[i],
                    user:     m1_axi4_ruser[i],
                    default:  '0}),
    .valid_i    (m1_axi4_rvalid[i]),
    .ready_o    (m1_axi4_rready[i]),
    .data_o     (r_buf_m1_oup),
    .valid_o    (int_m1_rvalid[i]),
    .ready_i    (int_m1_rready[i]),
    .usage_o    (/* unused */)
  );
  assign int_m1_rid[i]   = r_buf_m1_oup.id;
  assign int_m1_rresp[i] = r_buf_m1_oup.resp;
  assign int_m1_rdata[i] = r_buf_m1_oup.data;
  assign int_m1_rlast[i] = r_buf_m1_oup.last;
  assign int_m1_ruser[i] = r_buf_m1_oup.user;

  axi4_r_sender
    #(
      .AXI_DATA_WIDTH  ( AXI_DATA_WIDTH ),
      .AXI_ID_WIDTH    ( AXI_ID_WIDTH   ),
      .AXI_USER_WIDTH  ( AXI_USER_WIDTH )
      )
    u_r_sender
    (
      .axi4_aclk     ( Clk_CI              ),
      .axi4_arstn    ( Rst_RBI             ),
      .drop_i        ( lx_r_drop[i]        ),
      .drop_len_i    ( lx_len_drop[i]      ),
      .done_o        ( lx_r_done[i]        ),
      .id_i          ( lx_id_drop[i]       ),
      .prefetch_i    ( lx_prefetch_drop[i] ),
      .hit_i         ( lx_hit_drop[i]      ),
      .s_axi4_rid    ( s_axi4_rid[i]       ),
      .s_axi4_rresp  ( s_axi4_rresp[i]     ),
      .s_axi4_rdata  ( s_axi4_rdata[i]     ),
      .s_axi4_rlast  ( s_axi4_rlast[i]     ),
      .s_axi4_rvalid ( s_axi4_rvalid[i]    ),
      .s_axi4_ruser  ( s_axi4_ruser[i]     ),
      .s_axi4_rready ( s_axi4_rready[i]    ),
      .m_axi4_rid    ( int_rid[i]          ),
      .m_axi4_rresp  ( int_rresp[i]        ),
      .m_axi4_rdata  ( int_rdata[i]        ),
      .m_axi4_rlast  ( int_rlast[i]        ),
      .m_axi4_rvalid ( int_rvalid[i]       ),
      .m_axi4_ruser  ( int_ruser[i]        ),
      .m_axi4_rready ( int_rready[i]       )
    );

  /*
   * Multiplexer to switch between the two output master ports on the read response(r) channel
   *
   * Do not perform read burst interleaving as the DMA does not support it. This means we can only
   * switch between the two masters upon sending rlast or when idle.
   *
   * However, if the downstream already performs burst interleaving, this cannot be undone here.
   * Also, the downstream may interleave a burst reponse with a single-beat transaction. In this
   * case, the FSM below falls out of the burst mode. To avoid it performing burst interleaving
   * after such an event, it gives priority to the master which received the last burst in case
   * both have a have a burst ready (rvalid).
   *
   * Order of priority:
   * 1. Ongoing burst transaction
   * 2. Single-beat transaction on Master 1.
   * 3. Single-beat transaction on Master 0.
   * 4. Burst transaction on master that received the last burst.
   */
  // Select signal
  always_ff @(posedge Clk_CI) begin
    if (Rst_RBI == 0) begin
      RRespSel_SP[i] <= 1'b0;
    end else begin
      RRespSel_SP[i] <= RRespSel_SN[i];
    end
  end

  // FSM
  always_comb begin : RRespMuxFsm
    RRespMuxCtrl_SN[i] = RRespMuxCtrl_SP[i];
    RRespSel_SN[i]     = RRespSel_SP[i];

    RRespBurst_S[i]    = 1'b0;
    RRespSelIm_S[i]    = 1'b0;

    unique case (RRespMuxCtrl_SP[i])

      IDLE: begin
        // immediately forward single-beat transactions
        if      (int_m1_rvalid[i] && int_m1_rlast[i])
          RRespSelIm_S[i] = 1'b1;
        else if (int_m0_rvalid[i] && int_m0_rlast[i])
          RRespSelIm_S[i] = 1'b0;

        // bursts - they also start immediately
        else if (int_m1_rvalid[i] || int_m0_rvalid[i]) begin
          RRespMuxCtrl_SN[i] = BUSY;

          // in case both are ready, continue with the master that had the last burst
          if    (int_m1_rvalid[i] && int_m0_rvalid[i]) begin
            RRespSel_SN[i]  = RRespSel_SP[i];
            RRespSelIm_S[i] = RRespSel_SP[i];
          end else if (int_m1_rvalid[i]) begin
            RRespSel_SN[i]  = 1'b1;
            RRespSelIm_S[i] = 1'b1;
          end else begin
            RRespSel_SN[i]  = 1'b0;
            RRespSelIm_S[i] = 1'b0;
          end
        end
      end

      BUSY: begin
        RRespBurst_S[i] = 1'b1;
        // detect last handshake of currently ongoing transfer
        if (int_rvalid[i] && int_rready[i] && int_rlast[i])
          RRespMuxCtrl_SN[i] = IDLE;
      end

      default: begin
        RRespMuxCtrl_SN[i] = IDLE;
      end

    endcase
  end

  // FSM state
  always_ff @(posedge Clk_CI) begin
    if (Rst_RBI == 0) begin
      RRespMuxCtrl_SP[i] <= IDLE;
    end else begin
      RRespMuxCtrl_SP[i] <= RRespMuxCtrl_SN[i];
    end
  end

  // Actual multiplexer
  always_comb begin
    if ( (RRespBurst_S[i] && RRespSel_SP[i]) || (!RRespBurst_S[i] && RRespSelIm_S[i]) ) begin
      int_m0_rready[i] = 1'b0;
      int_m1_rready[i] = int_rready[i];

      int_rid[i]    = int_m1_rid[i];
      int_rresp[i]  = int_m1_rresp[i];
      int_rdata[i]  = int_m1_rdata[i];
      int_rlast[i]  = int_m1_rlast[i];
      int_ruser[i]  = int_m1_ruser[i];
      int_rvalid[i] = int_m1_rvalid[i];
    end else begin
      int_m0_rready[i] = int_rready[i];
      int_m1_rready[i] = 1'b0;

      int_rid[i]    = int_m0_rid[i];
      int_rresp[i]  = int_m0_rresp[i];
      int_rdata[i]  = int_m0_rdata[i];
      int_rlast[i]  = int_m0_rlast[i];
      int_ruser[i]  = int_m0_ruser[i];
      int_rvalid[i] = int_m0_rvalid[i];
    end
  end

  end // BUF & SEND

  // }}}

  endgenerate // BUF & SEND }}}

  // Log {{{

`ifdef RAB_AX_LOG_EN
  AxiBramLogger
    #(
      .AXI_ID_BITW     ( AXI_ID_WIDTH        ),
      .AXI_ADDR_BITW   ( AXI_S_ADDR_WIDTH    ),
      .NUM_LOG_ENTRIES ( `RAB_AX_LOG_ENTRIES )
    )
    u_aw_logger
    (
      .Clk_CI          ( NonGatedClk_CI    ),
      .TimestampClk_CI ( Clk_CI            ),
      .Rst_RBI         ( Rst_RBI           ),
      .AxiValid_SI     ( s_axi4_awvalid[1] ),
      .AxiReady_SI     ( s_axi4_awready[1] ),
      .AxiId_DI        ( s_axi4_awid[1]    ),
      .AxiAddr_DI      ( s_axi4_awaddr[1]  ),
      .AxiLen_DI       ( s_axi4_awlen[1]   ),
      .Clear_SI        ( AwLogClr_SI       ),
      .LogEn_SI        ( LogEn_SI          ),
      .Full_SO         ( int_aw_log_full   ),
      .Ready_SO        ( AwLogRdy_SO       ),
      .Bram_PS         ( AwBram_PS         )
    );

  AxiBramLogger
    #(
      .AXI_ID_BITW     ( AXI_ID_WIDTH        ),
      .AXI_ADDR_BITW   ( AXI_S_ADDR_WIDTH    ),
      .NUM_LOG_ENTRIES ( `RAB_AX_LOG_ENTRIES )
    )
    u_ar_logger
    (
      .Clk_CI          ( NonGatedClk_CI    ),
      .TimestampClk_CI ( Clk_CI            ),
      .Rst_RBI         ( Rst_RBI           ),
      .AxiValid_SI     ( s_axi4_arvalid[1] ),
      .AxiReady_SI     ( s_axi4_arready[1] ),
      .AxiId_DI        ( s_axi4_arid[1]    ),
      .AxiAddr_DI      ( s_axi4_araddr[1]  ),
      .AxiLen_DI       ( s_axi4_arlen[1]   ),
      .Clear_SI        ( ArLogClr_SI       ),
      .LogEn_SI        ( LogEn_SI          ),
      .Full_SO         ( int_ar_log_full   ),
      .Ready_SO        ( ArLogRdy_SO       ),
      .Bram_PS         ( ArBram_PS         )
    );
`endif

  // }}}

  // RAB Core {{{
  // ██████╗  █████╗ ██████╗      ██████╗ ██████╗ ██████╗ ███████╗
  // ██╔══██╗██╔══██╗██╔══██╗    ██╔════╝██╔═══██╗██╔══██╗██╔════╝
  // ██████╔╝███████║██████╔╝    ██║     ██║   ██║██████╔╝█████╗
  // ██╔══██╗██╔══██║██╔══██╗    ██║     ██║   ██║██╔══██╗██╔══╝
  // ██║  ██║██║  ██║██████╔╝    ╚██████╗╚██████╔╝██║  ██║███████╗
  // ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝      ╚═════╝ ╚═════╝ ╚═╝  ╚═╝╚══════╝
  //
  /*
   * rab_core
   *
   * The rab core translates addresses. It has two ports, which can be used
   * independently, however they will compete for time internally, as lookups
   * are serialized.
   *
   * type is the read(0) or write(1) used to check the protection flags. If they
   * don't match an interrupt is created on the int_prot line.
   */

  rab_core
    #(
      .N_PORTS             ( N_PORTS             ),
      .N_L1_SLICES         ( N_L1_SLICES         ),
      .N_L1_SLICES_MAX     ( N_L1_SLICES_MAX     ),
      .EN_ACP              ( EN_ACP              ),
      .ENABLE_L2TLB        ( ENABLE_L2TLB        ),
      .N_L2_SETS           ( N_L2_SETS           ),
      .N_L2_SET_ENTRIES    ( N_L2_SET_ENTRIES    ),
      .AXI_DATA_WIDTH      ( AXI_DATA_WIDTH      ),
      .AXI_S_ADDR_WIDTH    ( AXI_S_ADDR_WIDTH    ),
      .AXI_M_ADDR_WIDTH    ( AXI_M_ADDR_WIDTH    ),
      .AXI_LITE_DATA_WIDTH ( AXI_LITE_DATA_WIDTH ),
      .AXI_LITE_ADDR_WIDTH ( AXI_LITE_ADDR_WIDTH ),
      .AXI_ID_WIDTH        ( AXI_ID_WIDTH        ),
      .AXI_USER_WIDTH      ( AXI_USER_WIDTH      ),
      .MH_FIFO_DEPTH       ( MH_FIFO_DEPTH       )
    )
    u_rab_core
    (
      .Clk_CI               ( Clk_CI                     ),
      .Rst_RBI              ( Rst_RBI                    ),

      // Config IF
      .s_axi_awaddr         ( s_axi4lite_awaddr          ),
      .s_axi_awvalid        ( s_axi4lite_awvalid         ),
      .s_axi_awready        ( s_axi4lite_awready         ),
      .s_axi_wdata          ( s_axi4lite_wdata           ),
      .s_axi_wstrb          ( s_axi4lite_wstrb           ),
      .s_axi_wvalid         ( s_axi4lite_wvalid          ),
      .s_axi_wready         ( s_axi4lite_wready          ),
      .s_axi_bresp          ( s_axi4lite_bresp           ),
      .s_axi_bvalid         ( s_axi4lite_bvalid          ),
      .s_axi_bready         ( s_axi4lite_bready          ),
      .s_axi_araddr         ( s_axi4lite_araddr          ),
      .s_axi_arvalid        ( s_axi4lite_arvalid         ),
      .s_axi_arready        ( s_axi4lite_arready         ),
      .s_axi_rready         ( s_axi4lite_rready          ),
      .s_axi_rdata          ( s_axi4lite_rdata           ),
      .s_axi_rresp          ( s_axi4lite_rresp           ),
      .s_axi_rvalid         ( s_axi4lite_rvalid          ),

      // L1 miss info outputs -> L2 TLB arbitration
      .int_miss             ( rab_miss                   ),
      .int_multi            ( rab_multi                  ),
      .int_prot             ( rab_prot                   ),
      .int_prefetch         ( rab_prefetch               ),
      .int_invalidate       ( rab_invalidate             ),
      .int_mhf_full         ( int_mhf_full               ),

      // L1 transaction info outputs -> L2 TLB arbitration
      .int_axaddr_min_o     ( L1OutMinAddr_D             ),
      .int_axaddr_max_o     ( L1OutMaxAddr_D             ),
      .int_axid_o           ( L1OutId_D                  ),
      .int_axlen_o          ( L1OutLen_D                 ),
      .int_axuser_o         ( L1OutUser_D                ),

      // Write Req IF
      .port1_addr           ( int_awaddr                 ),
      .port1_id             ( int_awid                   ),
      .port1_len            ( int_awlen                  ),
      .port1_size           ( int_awsize                 ),
      .port1_addr_valid     ( int_awvalid & ~aw_in_stall ), // avoid the FSM accepting new AW requests
      .port1_type           ( {N_PORTS{1'b1}}            ),
      .port1_user           ( int_awuser                 ),
      .port1_sent           ( int_wtrans_sent            ), // signal done to L1 FSM
      .port1_out_addr       ( int_wtrans_addr            ),
      .port1_cache_coherent ( int_wtrans_cache_coherent  ),
      .port1_accept         ( int_wtrans_accept          ),
      .port1_drop           ( int_wtrans_drop            ),
      .port1_miss           ( int_wtrans_miss            ),

      // Read Req IF
      .port2_addr           ( int_araddr                 ),
      .port2_id             ( int_arid                   ),
      .port2_len            ( int_arlen                  ),
      .port2_size           ( int_arsize                 ),
      .port2_addr_valid     ( int_arvalid                ),
      .port2_type           ( {N_PORTS{1'b0}}            ),
      .port2_user           ( int_aruser                 ),
      .port2_sent           ( int_rtrans_sent            ), // signal done to L1 FSM
      .port2_out_addr       ( int_rtrans_addr            ),
      .port2_cache_coherent ( int_rtrans_cache_coherent  ),
      .port2_accept         ( int_rtrans_accept          ),
      .port2_drop           ( int_rtrans_drop            ),
      .port2_miss           ( int_rtrans_miss            ),

      // L2 miss info inputs -> axi_rab_cfg
      .miss_l2_i            ( L2Miss_S                   ),
      .miss_l2_addr_i       ( L2OutInAddr_DP             ),
      .miss_l2_id_i         ( L2OutId_DP                 ),
      .miss_l2_user_i       ( L2OutUser_DP               ),

      // L2 config outputs
      .wdata_l2_o           ( L2CfgWData_D               ),
      .waddr_l2_o           ( L2CfgWAddr_D               ),
      .wren_l2_o            ( L2CfgWE_S                  ),

      // L2 invalidation done
      .invalidate_l2_done_i ( l2_invalidate_done         )
    );

  // }}}

  // AX SPLITS {{{
  //  █████╗ ██╗  ██╗    ███████╗██████╗ ██╗     ██╗████████╗
  // ██╔══██╗╚██╗██╔╝    ██╔════╝██╔══██╗██║     ██║╚══██╔══╝
  // ███████║ ╚███╔╝     ███████╗██████╔╝██║     ██║   ██║
  // ██╔══██║ ██╔██╗     ╚════██║██╔═══╝ ██║     ██║   ██║
  // ██║  ██║██╔╝ ██╗    ███████║██║     ███████╗██║   ██║
  // ╚═╝  ╚═╝╚═╝  ╚═╝    ╚══════╝╚═╝     ╚══════╝╚═╝   ╚═╝
  //
  /**
   * Multiplex the two output master ports of the Read Address and Write Address (AR/AW) channels.
   *
   * Use the `int_xmaster_select` signal to route the signals to either Master 0 (to memory) or
   * Master 1 (to ACP). In case of an L1 miss: Route the signals to both masters. They shall be
   * saved until the L2 outputs are available.
   */
  generate for (i = 0; i < N_PORTS; i++) begin : AX_SPLIT

    /*
     * When accepting L1 transactions, we must just do so on the selected master. Drop requests must
     * be performed on any one of the two masters. Save requests must be performed by both masters.
     */
    always_comb begin : AW_L1_SPLIT

      // TLB handshake
      l1_m0_aw_accept[i] = 1'b0;
      l1_m1_aw_accept[i] = 1'b0;
      l1_m0_aw_drop[i]   = 1'b0;
      l1_m1_aw_drop[i]   = 1'b0;
      l1_m0_aw_save[i]   = 1'b0;
      l1_m1_aw_save[i]   = 1'b0;

      l1_mx_aw_done[i]   = 1'b0;

      // AXI sender input handshake
      int_m0_awvalid[i]  = 1'b0;
      int_m1_awvalid[i]  = 1'b0;
      int_awready[i]     = 1'b0;

      // accept on selected master only
      if (l1_aw_accept[i]) begin
        if (int_wmaster_select[i]) begin
          l1_m1_aw_accept[i] = 1'b1;
          l1_mx_aw_done[i]   = l1_m1_aw_done[i];

          int_m1_awvalid[i]  = int_awvalid[i];
          int_awready[i]     = int_m1_awready[i];

        end else begin
          l1_m0_aw_accept[i] = 1'b1;
          l1_mx_aw_done[i]   = l1_m0_aw_done[i];

          int_m0_awvalid[i]  = int_awvalid[i];
          int_awready[i]     = int_m0_awready[i];
        end

      // drop on Master 0 only
      end else if (l1_aw_drop[i]) begin
        l1_m0_aw_drop[i]     = 1'b1;
        l1_mx_aw_done[i]     = l1_m0_aw_done[i];

        int_m0_awvalid[i]    = int_awvalid[i];
        int_awready[i]       = l1_m0_aw_done[i];

      // save on both masters
      end else if (l1_aw_save[i]) begin
        // split save
        l1_m0_aw_save[i]     = ~l1_m0_aw_done_SP[i];
        l1_m1_aw_save[i]     = ~l1_m1_aw_done_SP[i];

        // combine done
        l1_mx_aw_done[i]     = l1_m0_aw_done_SP[i] & l1_m1_aw_done_SP[i];

        int_m0_awvalid[i]    = int_awvalid[i];
        int_m1_awvalid[i]    = int_awvalid[i];
        int_awready[i]       = l1_mx_aw_done[i];
      end
    end

    // signal back to handshake splitter
    assign l1_aw_done[i]     = l1_mx_aw_done[i];

    always_ff @(posedge Clk_CI) begin : L1_MX_AW_DONE_REG
      if (Rst_RBI == 0) begin
        l1_m0_aw_done_SP[i] <= 1'b0;
        l1_m1_aw_done_SP[i] <= 1'b0;
      end else if (l1_mx_aw_done[i]) begin
        l1_m0_aw_done_SP[i] <= 1'b0;
        l1_m1_aw_done_SP[i] <= 1'b0;
      end else begin
        l1_m0_aw_done_SP[i] <= l1_m0_aw_done_SP[i] | l1_m0_aw_done[i];
        l1_m1_aw_done_SP[i] <= l1_m1_aw_done_SP[i] | l1_m1_aw_done[i];
      end
    end

    /*
     * When accepting L2 transactions, we must drop the corresponding transaction from the other
     * master to make it available again for save requests from L1_DROP_SAVE.
     */
    always_comb begin : AW_L2_SPLIT

      l2_m0_aw_accept[i] = 1'b0;
      l2_m1_aw_accept[i] = 1'b0;
      l2_m0_aw_drop[i]   = 1'b0;
      l2_m1_aw_drop[i]   = 1'b0;

      // de-assert request signals individually upon handshakes
      if (l2_aw_accept[i]) begin
        if (l2_master_select[i]) begin
          l2_m1_aw_accept[i] = ~l2_m1_aw_done_SP[i];
          l2_m0_aw_drop[i]   = ~l2_m0_aw_done_SP[i];

        end else begin
          l2_m0_aw_accept[i] = ~l2_m0_aw_done_SP[i];
          l2_m1_aw_drop[i]   = ~l2_m1_aw_done_SP[i];

        end
      end else begin
        l2_m0_aw_drop[i]     = ~l2_m0_aw_done_SP[i] ? l2_aw_drop[i] : 1'b0;
        l2_m1_aw_drop[i]     = ~l2_m1_aw_done_SP[i] ? l2_aw_drop[i] : 1'b0;

      end

      // combine done
      l2_mx_aw_done[i] = l2_m0_aw_done_SP[i] & l2_m1_aw_done_SP[i];

      l2_aw_done[i]    = l2_mx_aw_done[i];
    end

    always_ff @(posedge Clk_CI) begin : L2_MX_AW_DONE_REG
      if (Rst_RBI == 0) begin
        l2_m0_aw_done_SP[i] <= 1'b0;
        l2_m1_aw_done_SP[i] <= 1'b0;
      end else if (l2_mx_aw_done[i]) begin
        l2_m0_aw_done_SP[i] <= 1'b0;
        l2_m1_aw_done_SP[i] <= 1'b0;
      end else begin
        l2_m0_aw_done_SP[i] <= l2_m0_aw_done_SP[i] | l2_m0_aw_done[i];
        l2_m1_aw_done_SP[i] <= l2_m1_aw_done_SP[i] | l2_m1_aw_done[i];
      end
    end

    /*
     * When accepting L1 transactions, we must just do so on the selected master. Drop requests must
     * be performed on any one of the two masters. Save requests must be performed by both masters.
     */
    always_comb begin : AR_L1_SPLIT

      // TLB handshake
      l1_m0_ar_accept[i] = 1'b0;
      l1_m1_ar_accept[i] = 1'b0;
      l1_m0_ar_drop[i]   = 1'b0;
      l1_m1_ar_drop[i]   = 1'b0;
      l1_m0_ar_save[i]   = 1'b0;
      l1_m1_ar_save[i]   = 1'b0;

      l1_mx_ar_done[i]   = 1'b0;

      // AXI sender input handshake
      int_m0_arvalid[i]  = 1'b0;
      int_m1_arvalid[i]  = 1'b0;
      int_arready[i]     = 1'b0;

      // accept on selected master only
      if (l1_ar_accept[i]) begin
        if (int_rmaster_select[i]) begin
          l1_m1_ar_accept[i] = 1'b1;
          l1_mx_ar_done[i]   = l1_m1_ar_done[i];

          int_m1_arvalid[i]  = int_arvalid[i];
          int_arready[i]     = int_m1_arready[i];

        end else begin
          l1_m0_ar_accept[i] = 1'b1;
          l1_mx_ar_done[i]   = l1_m0_ar_done[i];

          int_m0_arvalid[i]  = int_arvalid[i];
          int_arready[i]     = int_m0_arready[i];
        end

      // drop on Master 0 only
      end else if (l1_ar_drop[i]) begin
        l1_m0_ar_drop[i]     = 1'b1;
        l1_mx_ar_done[i]     = l1_m0_ar_done[i];

        int_m0_arvalid[i]    = int_arvalid[i];
        int_arready[i]       = l1_m0_ar_done[i];

      // save on both masters
      end else if (l1_ar_save[i]) begin
        // split save
        l1_m0_ar_save[i]     = ~l1_m0_ar_done_SP[i];
        l1_m1_ar_save[i]     = ~l1_m1_ar_done_SP[i];

        // combine done
        l1_mx_ar_done[i]     = l1_m0_ar_done_SP[i] & l1_m1_ar_done_SP[i];

        int_m0_arvalid[i]    = int_arvalid[i];
        int_m1_arvalid[i]    = int_arvalid[i];
        int_arready[i]       = l1_mx_ar_done[i];
      end
    end

    // signal back to handshake splitter
    assign l1_ar_done[i]     = l1_mx_ar_done[i];

    always_ff @(posedge Clk_CI) begin : L1_MX_AR_DONE_REG
      if (Rst_RBI == 0) begin
        l1_m0_ar_done_SP[i] <= 1'b0;
        l1_m1_ar_done_SP[i] <= 1'b0;
      end else if (l1_mx_ar_done[i]) begin
        l1_m0_ar_done_SP[i] <= 1'b0;
        l1_m1_ar_done_SP[i] <= 1'b0;
      end else begin
        l1_m0_ar_done_SP[i] <= l1_m0_ar_done_SP[i] | l1_m0_ar_done[i];
        l1_m1_ar_done_SP[i] <= l1_m1_ar_done_SP[i] | l1_m1_ar_done[i];
      end
    end

    /*
     * When accepting L2 transactions, we must drop the corresponding transaction from the other
     * master to make it available again for save requests from L1_DROP_SAVE.
     */
    always_comb begin : AR_L2_SPLIT

      l2_m0_ar_accept[i] = 1'b0;
      l2_m1_ar_accept[i] = 1'b0;
      l2_m0_ar_drop[i]   = 1'b0;
      l2_m1_ar_drop[i]   = 1'b0;

      // de-assert request signals individually upon handshakes
      if (l2_ar_accept[i]) begin
        if (l2_master_select[i]) begin
          l2_m1_ar_accept[i] = ~l2_m1_ar_done_SP[i];
          l2_m0_ar_drop[i]   = ~l2_m0_ar_done_SP[i];

        end else begin
          l2_m0_ar_accept[i] = ~l2_m0_ar_done_SP[i];
          l2_m1_ar_drop[i]   = ~l2_m1_ar_done_SP[i];

        end
      end else if (l2_ar_drop[i]) begin
        l2_m0_ar_drop[i]     = ~l2_m0_ar_done_SP[i] ? l2_ar_drop[i] : 1'b0;
        l2_m1_ar_drop[i]     = ~l2_m1_ar_done_SP[i] ? l2_ar_drop[i] : 1'b0;

      end

      // combine done
      l2_mx_ar_done[i] = l2_m0_ar_done_SP[i] & l2_m1_ar_done_SP[i];

      l2_ar_done[i]    = l2_mx_ar_done[i];
    end

    always_ff @(posedge Clk_CI) begin : L2_MX_AR_DONE_REG
      if (Rst_RBI == 0) begin
        l2_m0_ar_done_SP[i] <= 1'b0;
        l2_m1_ar_done_SP[i] <= 1'b0;
      end else if (l2_mx_ar_done[i]) begin
        l2_m0_ar_done_SP[i] <= 1'b0;
        l2_m1_ar_done_SP[i] <= 1'b0;
      end else begin
        l2_m0_ar_done_SP[i] <= l2_m0_ar_done_SP[i] | l2_m0_ar_done[i];
        l2_m1_ar_done_SP[i] <= l2_m1_ar_done_SP[i] | l2_m1_ar_done[i];
      end
    end

  end // AX_SPLIT
  endgenerate // AX_SPLIT

  // }}}

  // HANDSHAKE SPLITS {{{
  // ██╗  ██╗███████╗    ███████╗██████╗ ██╗     ██╗████████╗
  // ██║  ██║██╔════╝    ██╔════╝██╔══██╗██║     ██║╚══██╔══╝
  // ███████║███████╗    ███████╗██████╔╝██║     ██║   ██║
  // ██╔══██║╚════██║    ╚════██║██╔═══╝ ██║     ██║   ██║
  // ██║  ██║███████║    ███████║██║     ███████╗██║   ██║
  // ╚═╝  ╚═╝╚══════╝    ╚══════╝╚═╝     ╚══════╝╚═╝   ╚═╝
  //
  /*
   * We need to perform combined handshakes with multiple AXI modules
   * upon transactions drops, accepts, saves etc. from two TLBs.
   */
  generate for (i = 0; i < N_PORTS; i++) begin : HANDSHAKE_SPLIT

    assign l1_xw_accept[i]    = int_wtrans_accept[i] & ~aw_out_stall[i];
    assign int_wtrans_sent[i] = l1_xw_done[i];

    assign l1_ar_accept[i]    = int_rtrans_accept[i];
    assign int_rtrans_sent[i] = l1_ar_done[i];

    /*
     * L1 AW sender + W buffer handshake split
     */
    // forward
    assign l1_aw_accept[i] = l1_xw_accept[i] & ~l1_aw_done_SP[i];
    assign l1_w_accept[i]  = l1_xw_accept[i] & ~l1_w_done_SP[i];

    assign l1_aw_save[i]   = l1_xw_save[i]   & ~l1_aw_done_SP[i];
    assign l1_w_save[i]    = l1_xw_save[i]   & ~l1_w_done_SP[i];

    assign l1_aw_drop[i]   = l1_xw_drop[i]   & ~l1_aw_done_SP[i];
    assign l1_w_drop[i]    = l1_xw_drop[i]   & ~l1_w_done_SP[i];

    // backward
    assign l1_xw_done[i]   = l1_aw_done_SP[i] & l1_w_done_SP[i];

    always_ff @(posedge Clk_CI) begin : L1_XW_HS_SPLIT
      if (Rst_RBI == 0) begin
        l1_aw_done_SP[i] <= 1'b0;
        l1_w_done_SP[i]  <= 1'b0;
      end else if (l1_xw_done[i]) begin
        l1_aw_done_SP[i] <= 1'b0;
        l1_w_done_SP[i]  <= 1'b0;
      end else begin
        l1_aw_done_SP[i] <= l1_aw_done_SP[i] | l1_aw_done[i];
        l1_w_done_SP[i]  <= l1_w_done_SP[i]  | l1_w_done[i];
      end
    end

    if (ENABLE_L2TLB[i] == 1) begin : L2_HS_SPLIT

      /*
       * L1 AR sender + R sender handshake split
       *
       * AR and R do not need to be strictly in sync. We thus use separate handshakes.
       * But the handshake signals for the R sender are multiplexed with the those for
       * the L2. However, L2_ACCEPT_DROP_SAVE has always higher priority.
       */
      assign lx_r_drop[i] = l2_r_drop[i] | l1_r_drop[i];
      assign l1_r_done[i] = l2_r_drop[i] ? 1'b0         : lx_r_done[i];
      assign l2_r_done[i] = l2_r_drop[i] ? lx_r_done[i] : 1'b0;

      /*
       * L2 AW sender + W buffer handshake split
       */
      // forward
      assign l2_aw_accept[i] = l2_xw_accept[i] & ~l2_aw_done_SP[i];
      assign l2_w_accept[i]  = l2_xw_accept[i] & ~l2_w_done_SP[i];

      assign l2_aw_drop[i]   = l2_xw_drop[i]   & ~l2_aw_done_SP[i];
      assign l2_w_drop[i]    = l2_xw_drop[i]   & ~l2_w_done_SP[i];

      // backward
      assign l2_xw_done[i]   = l2_aw_done_SP[i] & l2_w_done_SP[i];

      always_ff @(posedge Clk_CI) begin : L2_XW_HS_SPLIT
        if (Rst_RBI == 0) begin
          l2_aw_done_SP[i] <= 1'b0;
          l2_w_done_SP[i]  <= 1'b0;
        end else if (l2_xw_done[i]) begin
          l2_aw_done_SP[i] <= 1'b0;
          l2_w_done_SP[i]  <= 1'b0;
        end else begin
          l2_aw_done_SP[i] <= l2_aw_done_SP[i] | l2_aw_done[i];
          l2_w_done_SP[i]  <= l2_w_done_SP[i]  | l2_w_done[i];
        end
      end

      /*
       * L2 AR + R sender handshake split
       */
      // forward
      assign l2_ar_drop[i]   = l2_xr_drop[i]   & ~l2_ar_done_SP[i];
      assign l2_r_drop[i]    = l2_xr_drop[i]   & ~l2_r_done_SP[i];

      // backward - make sure to always clear L2_XR_HS_SPLIT
      always_comb begin
        if (l2_xr_drop[i]) begin
          l2_xr_done[i]      = l2_ar_done_SP[i] & l2_r_done_SP[i];
        end else begin
          l2_xr_done[i]      = l2_ar_done_SP[i];
        end
      end

      always_ff @(posedge Clk_CI) begin : L2_XR_HS_SPLIT
        if (Rst_RBI == 0) begin
          l2_ar_done_SP[i] <= 1'b0;
          l2_r_done_SP[i]  <= 1'b0;
        end else if (l2_xr_done[i]) begin
          l2_ar_done_SP[i] <= 1'b0;
          l2_r_done_SP[i]  <= 1'b0;
        end else begin
          l2_ar_done_SP[i] <= l2_ar_done_SP[i] | l2_ar_done[i];
          l2_r_done_SP[i]  <= l2_r_done_SP[i]  | l2_r_done[i];
        end
      end

    end else begin // if (ENABLE_L2TLB[i] == 1)

      assign lx_r_drop[i]     = l1_r_drop[i];
      assign l1_r_done[i]     = lx_r_done[i];

      assign l2_aw_accept[i]  = 1'b0;
      assign l2_w_accept[i]   = 1'b0;
      assign l2_aw_drop[i]    = 1'b0;
      assign l2_w_drop[i]     = 1'b0;
      assign l2_xw_done[i]    = 1'b0;
      assign l2_aw_done_SP[i] = 1'b0;
      assign l2_w_done_SP[i]  = 1'b0;

      assign l2_ar_accept[i]  = 1'b0;
      assign l2_ar_drop[i]    = 1'b0;
      assign l2_r_drop[i]     = 1'b0;
      assign l2_xr_done[i]    = 1'b0;
      assign l2_r_done[i]     = 1'b0;
      assign l2_ar_done_SP[i] = 1'b0;
      assign l2_r_done_SP[i]  = 1'b0;

    end // if (ENABLE_L2TLB[i] == 1)

  end // HANDSHAKE_SPLIT
  endgenerate // HANDSHAKE_SPLIT

  // }}}

  // L2 TLB {{{
  // ██╗     ██████╗     ████████╗██╗     ██████╗
  // ██║     ╚════██╗    ╚══██╔══╝██║     ██╔══██╗
  // ██║      █████╔╝       ██║   ██║     ██████╔╝
  // ██║     ██╔═══╝        ██║   ██║     ██╔══██╗
  // ███████╗███████╗       ██║   ███████╗██████╔╝
  // ╚══════╝╚══════╝       ╚═╝   ╚══════╝╚═════╝
  //
  /*
   * l2_tlb
   *
   * The L2 TLB translates addresses upon misses in the L1 TLB (rab_core).
   *
   * It supports one ongoing translation at a time. If an L1 miss occurs while the L2 is busy,
   * the L1 is stalled untill the L2 is available again.
   *
   */
  generate for (i = 0; i < N_PORTS; i++) begin : L2_TLB
    if (ENABLE_L2TLB[i] == 1) begin : L2_TLB

      /*
       * L1 output selector
       */
      assign L1OutRwType_D[i] = int_wtrans_drop[i] ? 1'b1 : 1'b0;
      assign L1OutProt_D[i]   = rab_prot[i];
      assign L1OutMulti_D[i]  = rab_multi[i];

      /*
       * L1 output control + L1_DROP_BUF, L2_IN_BUF management
       *
       * Forward the L1 drop request to AR/AW sender modules if
       * 1. the transactions needs to be dropped (L1 multi, prot, prefetch), or
       * 2. if a lookup in the L2 TLB is required (L1 miss) and the input buffer is not full.
       *
       * The AR/AW senders do not support more than 1 oustanding L1 miss. The push back towards
       * the upstream is realized by not accepting the save request (saving the L1 transaction)
       * in the senders as long as the L2 TLB is busy or has valid output. This ultimately
       * blocks the L1 TLB.
       *
       * Together with the AW drop/save, we also perform the W drop/save as AW and W need to
       * absolutely remain in order. In contrast, the R drop is performed
       */
      always_comb begin : L1_DROP_SAVE

        l1_ar_drop[i]       = 1'b0;
        l1_ar_save[i]       = 1'b0;
        l1_xw_drop[i]       = 1'b0;
        l1_xw_save[i]       = 1'b0;

        l1_id_drop[i]       = L1OutId_D[i];
        l1_len_drop[i]      = L1OutLen_D[i];
        l1_prefetch_drop[i] = rab_prefetch[i];
        l1_hit_drop[i]      = 1'b1; // there are no drops for L1 misses

        L1DropEn_S[i]       = 1'b0;
        L2InEn_S[i]         = 1'b0;

        l2_invalidate_in_progress_d[i] = l2_invalidate_in_progress_q[i] & rab_invalidate[i];

        if ( rab_invalidate[i] ) begin
          // 0. Forward invalidation to the L2 (if not done yet) without dropping any L1 request
          L2InEn_S[i]                    = ~L2Busy_S[i] & ~l2_invalidate_in_progress_q[i];
          if (L2InEn_S[i] == 1'b1) begin
            l2_invalidate_in_progress_d[i] = 1'b1;
          end
        end else if ( rab_prot[i] | rab_multi[i] | rab_prefetch[i] ) begin
          // 1. Drop
          l1_ar_drop[i] = int_rtrans_drop[i] & ~L1DropValid_SP[i];
          l1_xw_drop[i] = int_wtrans_drop[i] & ~L1DropValid_SP[i];

          // Store to L1_DROP_BUF upon handshake
          L1DropEn_S[i] = (l1_ar_drop[i] & l1_ar_done[i]) |
                          (l1_xw_drop[i] & l1_xw_done[i]);
        end else if ( rab_miss[i] ) begin
          // 2. Save - Make sure L2 is really available.
          l1_ar_save[i] = int_rtrans_drop[i] & ~L2Busy_S[i];
          l1_xw_save[i] = int_wtrans_drop[i] & ~L2Busy_S[i];

          // Store to L2_IN_BUF upon handshake - triggers the L2 TLB
          L2InEn_S[i]   = (l1_ar_save[i] & l1_ar_done[i]) |
                          (l1_xw_save[i] & l1_xw_done[i]);
        end
      end

      /*
       * L2 output control + L2_OUT_BUF management + R/B sender control + W buffer control
       *
       * Perform L1 R transaction drops unless the L2 output buffer holds valid data. The AXI specs
       * require the B response to be sent only after consuming/discarding the corresponding data
       * in the W channel. Thus, we only send L2 drop request to the W buffer here. The drop
       * request to the B sender is then sent by the W buffer autonomously.
       *
       * L1 AW/W drop requests are managed by L1_DROP_SAVE.
       */
      always_comb begin : L2_ACCEPT_DROP_SAVE

        l2_ar_addr[i]         =  'b0;
        l2_aw_addr[i]         =  'b0;
        l2_ar_accept[i]       = 1'b0;
        l2_xr_drop[i]         = 1'b0;
        l2_xw_accept[i]       = 1'b0;
        l2_xw_drop[i]         = 1'b0;

        l1_r_drop[i]          = 1'b0;

        lx_id_drop[i]         =  'b0;
        lx_len_drop[i]        =  'b0;
        lx_prefetch_drop[i]   = 1'b0;
        lx_hit_drop[i]        = 1'b0;

        L1DropValid_SN[i]     = L1DropValid_SP[i] | L1DropEn_S[i];
        L2OutValid_SN[i]      = L2OutValid_SP[i];
        L2OutReady_S[i]       = 1'b0;
        L2OutEn_S[i]          = 1'b0;

        L2Miss_S[i]           = 1'b0;
        int_multi[i]          = 1'b0;
        int_prot[i]           = 1'b0;

        l2_invalidate_done[i] = 1'b0;

        if (L2OutValid_SP[i] == 1'b0) begin

          // Drop L1 from R senders
          if (L1DropValid_SP[i] == 1'b1) begin

            // Only perform the R sender drop here.
            if (~L1DropRwType_DP[i]) begin

              l1_r_drop[i]        = 1'b1;
              lx_id_drop[i]       = L1DropId_DP[i];
              lx_len_drop[i]      = L1DropLen_DP[i];
              lx_prefetch_drop[i] = L1DropPrefetch_S[i];
              lx_hit_drop[i]      = 1'b1; // there are no drops for L1 misses

              // Invalidate L1_DROP_BUF upon handshake
              if ( l1_r_drop[i] & l1_r_done[i] ) begin

                L1DropValid_SN[i] = 1'b0;
                int_prot[i]       = L1DropProt_DP[i];
                int_multi[i]      = L1DropMulti_DP[i];
              end

            end else begin
              // Invalidate L1_DROP_BUF
              L1DropValid_SN[i]   = 1'b0;
              int_prot[i]         = L1DropProt_DP[i];
              int_multi[i]        = L1DropMulti_DP[i];
            end
          end

        end else begin // L2_OUT_BUF has valid data

          if ( L2OutInvalidate_DP[i] ) begin
            // If invalidation raise the invalidation_done flag, and ignore rest of request
            l2_invalidate_done[i] = 1'b1; // will be saved by config block in next cycle
            L2OutValid_SN[i]      = 1'b0;
          end else begin
            if ( L2OutHit_SP[i] & ~(L2OutPrefetch_S[i] | L2OutProt_SP[i] | L2OutMulti_SP[i]) ) begin
              // If a hit is found set accept flag
              l2_ar_addr[i]       = L2OutAddr_DP[i];
              l2_aw_addr[i]       = L2OutAddr_DP[i];

              l2_ar_accept[i]     = L2OutRwType_DP[i] ? 1'b0 : 1'b1;
              l2_xw_accept[i]     = L2OutRwType_DP[i] ? 1'b1 : 1'b0;

              // Invalidate L2_OUT_BUF upon handshake
              L2OutValid_SN[i]    = ~((l2_ar_accept[i] & l2_ar_done[i]) |
                                      (l2_xw_accept[i] & l2_xw_done[i]));
            end else begin
              // In case of no hit or an error set drop flag
              lx_id_drop[i]       = L2OutId_DP[i];
              lx_len_drop[i]      = L2OutLen_DP[i];
              lx_prefetch_drop[i] = L2OutPrefetch_S[i];
              lx_hit_drop[i]      = L2OutHit_SP[i];

              // The l2_xr_drop will also perform the handshake with the R sender
              l2_xr_drop[i]       = L2OutRwType_DP[i] ? 1'b0 : 1'b1;
              l2_xw_drop[i]       = L2OutRwType_DP[i] ? 1'b1 : 1'b0;

              // Invalidate L1_DROP_BUF upon handshake
              if ( (l2_xr_drop[i] & l2_xr_done[i]) | (l2_xw_drop[i] & l2_xw_done[i]) ) begin

                L2OutValid_SN[i]  = 1'b0;
                L2Miss_S[i]       = ~L2OutHit_SP[i];
                int_prot[i]       = L2OutProt_SP[i];
                int_multi[i]      = L2OutMulti_SP[i];
              end
            end // else: !if( L2OutHit_SP[i] & ~(L2OutPrefetch_S[i] | L2OutProt_SP[i] | L2OutMulti_SP[i]) )
          end // else: !if( L2OutInvalidate_DP )
        end

        // Only accept new L2 output after ongoing drops have finished.
        if ( (l2_xr_drop[i] == l2_xr_done[i]) &
             (l2_xw_drop[i] == l2_xw_done[i]) &
             (l1_r_drop[i]  == l1_r_done[i] ) ) begin
          // Store to L2_OUT_BUF upon handshake with L2 TLB module
          if ( (L2OutValid_SP[i] == 1'b0) && (L2OutValid_S[i] == 1'b1) ) begin
            L2OutValid_SN[i]   = 1'b1;
            L2OutReady_S[i]    = 1'b1;
            L2OutEn_S[i]       = 1'b1;
          end
        end
      end

      /*
       * L1 drop buffer
       *
       * Used in case of multi, prot and prefetch hits in the L1 TLB.
       */
      always_ff @(posedge Clk_CI) begin : L1_DROP_BUF
         if (Rst_RBI == 0) begin
            L1DropProt_DP[i]   <= 1'b0;
            L1DropMulti_DP[i]  <= 1'b0;
            L1DropRwType_DP[i] <= 1'b0;
            L1DropUser_DP[i]   <=  'b0;
            L1DropId_DP[i]     <=  'b0;
            L1DropLen_DP[i]    <=  'b0;
            L1DropAddr_DP[i]   <=  'b0;
         end else if (L1DropEn_S[i] == 1'b1) begin
            L1DropProt_DP[i]   <= L1OutProt_D[i];
            L1DropMulti_DP[i]  <= L1OutMulti_D[i];
            L1DropRwType_DP[i] <= L1OutRwType_D[i];
            L1DropUser_DP[i]   <= L1OutUser_D[i];
            L1DropId_DP[i]     <= L1OutId_D[i];
            L1DropLen_DP[i]    <= L1OutLen_D[i];
            L1DropAddr_DP[i]   <= L1OutMinAddr_D[i];
         end
      end // always_ff @ (posedge Clk_CI)

      /*
       * L2 input buffer
       *
       * Make sure there are no combinational paths between L1 TLB/inputs and L2 TLB.
       */
      always_ff @(posedge Clk_CI) begin : L2_IN_BUF
         if (Rst_RBI == 0) begin
            L2InRwType_DP[i]     <= 1'b0;
            L2InUser_DP[i]       <=  'b0;
            L2InId_DP[i]         <=  'b0;
            L2InLen_DP[i]        <=  'b0;
            L2InMinAddr_DP[i]    <=  'b0;
            L2InMaxAddr_DP[i]    <=  'b0;
            L2InInvalidate_DP[i] <=  'b0;
         end else if (L2InEn_S[i] == 1'b1) begin
            L2InRwType_DP[i]     <= L1OutRwType_D[i];
            L2InUser_DP[i]       <= L1OutUser_D[i];
            L2InId_DP[i]         <= L1OutId_D[i];
            L2InLen_DP[i]        <= L1OutLen_D[i];
            L2InMinAddr_DP[i]    <= L1OutMinAddr_D[i];
            L2InMaxAddr_DP[i]    <= L1OutMaxAddr_D[i];
            L2InInvalidate_DP[i] <= rab_invalidate[i];
         end
      end // always_ff @ (posedge Clk_CI)

      /*
       * L2 invalidation logic
       *
       * Make sure every invalidation request is passed to the L2 only a single time
       */
      always_ff @(posedge Clk_CI or negedge Rst_RBI) begin
         if (Rst_RBI == 0) begin
            l2_invalidate_in_progress_q[i] = 'b0;
         end else begin
            l2_invalidate_in_progress_q[i] = l2_invalidate_in_progress_d[i];
         end
      end

      l2_tlb
        #(
          .AXI_S_ADDR_WIDTH       ( AXI_S_ADDR_WIDTH                            ),
          .AXI_M_ADDR_WIDTH       ( AXI_M_ADDR_WIDTH                            ),
          .AXI_LITE_DATA_WIDTH    ( AXI_LITE_DATA_WIDTH                         ),
          .AXI_LITE_ADDR_WIDTH    ( AXI_LITE_ADDR_WIDTH                         ),
          .N_SETS                 ( N_L2_SETS                                   ),
          .N_OFFSETS              ( N_L2_SET_ENTRIES/2/N_L2_PAR_VA_RAMS         ),
          .N_PAR_VA_RAMS          ( N_L2_PAR_VA_RAMS                            ),
          .HIT_OFFSET_STORE_WIDTH ( $clog2(N_L2_SET_ENTRIES/2/N_L2_PAR_VA_RAMS) )
          )
      u_l2_tlb
        (
          .clk_i              ( Clk_CI               ),
          .rst_ni             ( Rst_RBI              ),

          // Config inputs
          .we_i               ( L2CfgWE_S[i]         ),
          .waddr_i            ( L2CfgWAddr_D[i]      ),
          .wdata_i            ( L2CfgWData_D[i]      ),

          // Request input
          .start_i            ( L2InEn_S[i]          ),
          .busy_o             ( L2Busy_S[i]          ),
          .rw_type_i          ( L2InRwType_DP[i]     ),
          .in_addr_min_i      ( L2InMinAddr_DP[i]    ),
          .in_addr_max_i      ( L2InMaxAddr_DP[i]    ),
          .invalidate_i       ( L2InInvalidate_DP[i] ),

          // Response output
          .out_ready_i        ( L2OutReady_S[i]      ),
          .out_valid_o        ( L2OutValid_S[i]      ),
          .hit_o              ( L2OutHit_SN[i]       ),
          .miss_o             ( L2OutMiss_SN[i]      ),
          .prot_o             ( L2OutProt_SN[i]      ),
          .multi_o            ( L2OutMulti_SN[i]     ),
          .cache_coherent_o   ( L2OutCC_SN[i]        ),
          .out_addr_o         ( L2OutAddr_DN[i]      )
        );

      /*
       * L2 output buffer
       *
       * Make sure there are no combinational paths between L1 TLB/inputs and L2 TLB.
       */
      always_ff @(posedge Clk_CI) begin : L2_OUT_BUF
         if (Rst_RBI == 0) begin
            L2OutRwType_DP[i]     <= 1'b0;
            L2OutUser_DP[i]       <=  'b0;
            L2OutLen_DP[i]        <=  'b0;
            L2OutId_DP[i]         <=  'b0;
            L2OutInAddr_DP[i]     <=  'b0;
            L2OutInvalidate_DP[i] <=  'b0;

            L2OutHit_SP[i]        <= 1'b0;
            L2OutMiss_SP[i]       <= 1'b0;
            L2OutProt_SP[i]       <= 1'b0;
            L2OutMulti_SP[i]      <= 1'b0;
            L2OutCC_SP[i]         <= 1'b0;
            L2OutAddr_DP[i]       <=  'b0;
         end else if (L2OutEn_S[i] == 1'b1) begin
            L2OutRwType_DP[i]     <= L2InRwType_DP[i];
            L2OutUser_DP[i]       <= L2InUser_DP[i];
            L2OutLen_DP[i]        <= L2InLen_DP[i];
            L2OutId_DP[i]         <= L2InId_DP[i];
            L2OutInAddr_DP[i]     <= L2InMinAddr_DP[i];
            L2OutInvalidate_DP[i] <= L2InInvalidate_DP[i];

            L2OutHit_SP[i]        <= L2OutHit_SN[i];
            L2OutMiss_SP[i]       <= L2OutMiss_SN[i];
            L2OutProt_SP[i]       <= L2OutProt_SN[i];
            L2OutMulti_SP[i]      <= L2OutMulti_SN[i];
            L2OutCC_SP[i]         <= L2OutCC_SN[i];
            L2OutAddr_DP[i]       <= L2OutAddr_DN[i];
         end
      end // always_ff @ (posedge Clk_CI)

      always_ff @(posedge Clk_CI) begin : BUF_VALID
        if (Rst_RBI == 0) begin
          L1DropValid_SP[i] = 1'b0;
          L2OutValid_SP[i]  = 1'b0;
        end else begin
          L1DropValid_SP[i] = L1DropValid_SN[i];
          L2OutValid_SP[i]  = L2OutValid_SN[i];
        end
      end

      always_comb begin : BUF_TO_PREFETCH
        // L1 Drop Buf
        if (L1DropUser_DP[i] == {AXI_USER_WIDTH{1'b1}})
          L1DropPrefetch_S[i] = 1'b1;
        else
          L1DropPrefetch_S[i] = 1'b0;

        // L2 Out Buf
        if (L2OutUser_DP[i] == {AXI_USER_WIDTH{1'b1}})
          L2OutPrefetch_S[i]  = 1'b1;
        else
          L2OutPrefetch_S[i]  = 1'b0;
      end

      assign l2_cache_coherent[i] = L2OutCC_SP[i];
      assign int_miss[i]          = L2Miss_S[i];

    end else begin : L2_TLB_STUB // if (ENABLE_L2TLB[i] == 1)

      assign l1_ar_drop[i]                  = int_rtrans_drop[i];
      assign l1_r_drop[i]                   = int_rtrans_drop[i];
      assign l1_xw_drop[i]                  = int_wtrans_drop[i];

      assign l1_ar_save[i]                  = 1'b0;
      assign l1_xw_save[i]                  = 1'b0;
      assign l2_xw_accept[i]                = 1'b0;
      assign l2_xr_drop[i]                  = 1'b0;
      assign l2_xw_drop[i]                  = 1'b0;

      assign l2_ar_addr[i]                  =  'b0;
      assign l2_aw_addr[i]                  =  'b0;

      assign l1_id_drop[i]                  = int_wtrans_drop[i] ? int_awid[i] :
                                              int_rtrans_drop[i] ? int_arid[i] :
                                                '0;
      assign l1_len_drop[i]                 = int_wtrans_drop[i] ? int_awlen[i] :
                                              int_rtrans_drop[i] ? int_arlen[i] :
                                                '0;
      assign l1_prefetch_drop[i]            = rab_prefetch[i];
      assign l1_hit_drop[i]                 = ~rab_miss[i];

      assign lx_id_drop[i]                  = int_wtrans_drop[i] ? int_awid[i] :
                                              int_rtrans_drop[i] ? int_arid[i] :
                                              '0;
      assign lx_len_drop[i]                 = int_wtrans_drop[i] ? int_awlen[i] :
                                              int_rtrans_drop[i] ? int_arlen[i] :
                                              '0;
      assign lx_prefetch_drop[i]            = rab_prefetch[i];
      assign lx_hit_drop[i]                 = ~rab_miss[i];

      assign l2_cache_coherent[i]           = 1'b0;

      assign int_miss[i]                    = rab_miss[i];
      assign int_prot[i]                    = rab_prot[i];
      assign int_multi[i]                   = rab_multi[i];

      assign l2_invalidate_in_progress_d[i] = 1'b0;
      assign l2_invalidate_in_progress_q[i] = 1'b0;
      assign l2_invalidate_done[i]          = rab_invalidate[i];

      // unused signals
      assign L2Miss_S[i]                    = 1'b0;

      assign L1OutRwType_D[i]               = 1'b0;
      assign L1OutProt_D[i]                 = 1'b0;
      assign L1OutMulti_D[i]                = 1'b0;

      assign L1DropRwType_DP[i]             = 1'b0;
      assign L1DropUser_DP[i]               =  'b0;
      assign L1DropId_DP[i]                 =  'b0;
      assign L1DropLen_DP[i]                =  'b0;
      assign L1DropAddr_DP[i]               =  'b0;
      assign L1DropProt_DP[i]               = 1'b0;
      assign L1DropMulti_DP[i]              = 1'b0;

      assign L1DropEn_S[i]                  = 1'b0;
      assign L1DropPrefetch_S[i]            = 1'b0;
      assign L1DropValid_SN[i]              = 1'b0;
      assign L1DropValid_SP[i]              = 1'b0;

      assign L2InRwType_DP[i]               = 1'b0;
      assign L2InUser_DP[i]                 =  'b0;
      assign L2InId_DP[i]                   =  'b0;
      assign L2InLen_DP[i]                  =  'b0;
      assign L2InMinAddr_DP[i]              =  'b0;
      assign L2InMaxAddr_DP[i]              =  'b0;
      assign L2InInvalidate_DP[i]           =  'b0;

      assign L2InEn_S[i]                    = 1'b0;

      assign L2OutHit_SN[i]                 = 1'b0;
      assign L2OutMiss_SN[i]                = 1'b0;
      assign L2OutProt_SN[i]                = 1'b0;
      assign L2OutMulti_SN[i]               = 1'b0;
      assign L2OutCC_SN[i]                  = 1'b0;
      assign L2OutAddr_DN[i]                =  'b0;

      assign L2OutRwType_DP[i]              = 1'b0;
      assign L2OutUser_DP[i]                =  'b0;
      assign L2OutId_DP[i]                  =  'b0;
      assign L2OutLen_DP[i]                 =  'b0;
      assign L2OutInAddr_DP[i]              =  'b0;
      assign L2OutInvalidate_DP[i]          =  'b0;
      assign L2OutHit_SP[i]                 = 1'b0;
      assign L2OutMiss_SP[i]                = 1'b0;
      assign L2OutProt_SP[i]                = 1'b0;
      assign L2OutMulti_SP[i]               = 1'b0;
      assign L2OutCC_SP[i]                  = 1'b0;
      assign L2OutAddr_DP[i]                =  'b0;

      assign L2OutEn_S[i]                   = 1'b0;
      assign L2OutPrefetch_S[i]             = 1'b0;
      assign L2Busy_S[i]                    = 1'b0;
      assign L2OutValid_S[i]                = 1'b0;
      assign L2OutValid_SN[i]               = 1'b0;
      assign L2OutValid_SP[i]               = 1'b0;
      assign L2OutReady_S[i]                = 1'b0;

    end // !`ifdef ENABLE_L2TLB
  end // for (i = 0; i < N_PORTS; i++)
  endgenerate

// }}}

endmodule

// vim: ts=2 sw=2 sts=2 et nosmartindent autoindent foldmethod=marker
