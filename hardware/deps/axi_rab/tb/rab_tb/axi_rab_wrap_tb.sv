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
//  █████╗ ██╗  ██╗██╗    ██████╗  █████╗ ██████╗     ██╗    ██╗██████╗  █████╗ ██████╗
// ██╔══██╗╚██╗██╔╝██║    ██╔══██╗██╔══██╗██╔══██╗    ██║    ██║██╔══██╗██╔══██╗██╔══██╗
// ███████║ ╚███╔╝ ██║    ██████╔╝███████║██████╔╝    ██║ █╗ ██║██████╔╝███████║██████╔╝
// ██╔══██║ ██╔██╗ ██║    ██╔══██╗██╔══██║██╔══██╗    ██║███╗██║██╔══██╗██╔══██║██╔═══╝
// ██║  ██║██╔╝ ██╗██║    ██║  ██║██║  ██║██████╔╝    ╚███╔███╔╝██║  ██║██║  ██║██║
// ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝    ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝      ╚══╝╚══╝ ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝
//
// --=========================================================================--

`include "pulp_soc_defines.sv"

module axi_rab_wrap
  #(
    parameter N_SLICES               = 16,
    parameter AXI_EXT_ADDR_WIDTH     = 40,
    parameter AXI_ADDR_WIDTH         = 32,
    parameter AXI_DATA_WIDTH         = 64,
    parameter AXI_USER_WIDTH         = 6,
    parameter AXI_LITE_ADDR_WIDTH    = 32,
    parameter AXI_LITE_DATA_WIDTH    = 64,
    parameter AXI_ID_EXT_S_WIDTH     = 6,
    parameter AXI_ID_EXT_S_ACP_WIDTH = 6,
    parameter AXI_ID_EXT_M_WIDTH     = 14,
    parameter AXI_ID_SOC_S_WIDTH     = 7,
    parameter AXI_ID_SOC_M_WIDTH     = 10,
    parameter N_PORTS                = 1
    )
   (
    input  logic        clk_i,
    input  logic        rst_ni,

    AXI_BUS.Master rab_to_socbus,
    AXI_BUS.Slave  socbus_to_rab,

    AXI_BUS.Master rab_master,
`ifdef EN_ACP
    AXI_BUS.Master rab_acp,
`endif
    AXI_BUS.Slave  rab_slave,

    AXI_LITE.Slave rab_lite,

    output logic intr_miss_o ,
    output logic intr_multi_o,
    output logic intr_prot_o,
    output logic intr_mhf_full_o
    );

  localparam AXI_ID_WIDTH = FUNC_MAX(AXI_ID_SOC_S_WIDTH,AXI_ID_SOC_M_WIDTH);

  function int FUNC_MAX(int a, b);
   if (a > b)
     return a;
   else
     return b;
  endfunction

  AXI_BUS
  #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    )
  rab_acp_id_remap();

  axi_id_remap_wrap
  #(
    .AXI_ADDR_WIDTH   ( AXI_ADDR_WIDTH         ),
    .AXI_DATA_WIDTH   ( AXI_DATA_WIDTH         ),
    .AXI_USER_WIDTH   ( AXI_USER_WIDTH         ),
    .AXI_ID_IN_WIDTH  ( AXI_ID_WIDTH           ),
    .AXI_ID_OUT_WIDTH ( AXI_ID_EXT_S_ACP_WIDTH ),
    .AXI_ID_SLOT      ( 1                      )
  )
  ext_s_acp_id_remap_wrap_i
  (
    .clk_i     ( clk_i            ),
    .rst_ni    ( rst_ni           ),

    .axi_slave ( rab_acp_id_remap ),
    .axi_master( rab_acp          )
  );

  // ███████╗██╗ ██████╗ ███╗   ██╗ █████╗ ██╗     ███████╗
  // ██╔════╝██║██╔════╝ ████╗  ██║██╔══██╗██║     ██╔════╝
  // ███████╗██║██║  ███╗██╔██╗ ██║███████║██║     ███████╗
  // ╚════██║██║██║   ██║██║╚██╗██║██╔══██║██║     ╚════██║
  // ███████║██║╚██████╔╝██║ ╚████║██║  ██║███████╗███████║
  // ╚══════╝╚═╝ ╚═════╝ ╚═╝  ╚═══╝╚═╝  ╚═╝╚══════╝╚══════╝
  //

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] s_axi_awid;
  logic [N_PORTS-1:0]     [AXI_ADDR_WIDTH-1:0] s_axi_awaddr;
  logic [N_PORTS-1:0]                          s_axi_awvalid;
  logic [N_PORTS-1:0]                          s_axi_awready;
  logic [N_PORTS-1:0]                    [7:0] s_axi_awlen;
  logic [N_PORTS-1:0]                    [2:0] s_axi_awsize;
  logic [N_PORTS-1:0]                    [1:0] s_axi_awburst;
  logic [N_PORTS-1:0]                          s_axi_awlock;
  logic [N_PORTS-1:0]                    [2:0] s_axi_awprot;
  logic [N_PORTS-1:0]                    [3:0] s_axi_awcache;
  logic [N_PORTS-1:0]                    [3:0] s_axi_awregion;
  logic [N_PORTS-1:0]                    [3:0] s_axi_awqos;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] s_axi_awuser;

  logic [N_PORTS-1:0]     [AXI_DATA_WIDTH-1:0] s_axi_wdata;
  logic [N_PORTS-1:0]                          s_axi_wvalid;
  logic [N_PORTS-1:0]                          s_axi_wready;
  logic [N_PORTS-1:0]   [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb;
  logic [N_PORTS-1:0]                          s_axi_wlast;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] s_axi_wuser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] s_axi_bid;
  logic [N_PORTS-1:0]                    [1:0] s_axi_bresp;
  logic [N_PORTS-1:0]                          s_axi_bvalid;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] s_axi_buser;
  logic [N_PORTS-1:0]                          s_axi_bready;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] s_axi_arid;
  logic [N_PORTS-1:0]     [AXI_ADDR_WIDTH-1:0] s_axi_araddr;
  logic [N_PORTS-1:0]                          s_axi_arvalid;
  logic [N_PORTS-1:0]                          s_axi_arready;
  logic [N_PORTS-1:0]                    [7:0] s_axi_arlen;
  logic [N_PORTS-1:0]                    [2:0] s_axi_arsize;
  logic [N_PORTS-1:0]                    [1:0] s_axi_arburst;
  logic [N_PORTS-1:0]                          s_axi_arlock;
  logic [N_PORTS-1:0]                    [2:0] s_axi_arprot;
  logic [N_PORTS-1:0]                    [3:0] s_axi_arcache;
  logic [N_PORTS-1:0]                    [3:0] s_axi_arregion;
  logic [N_PORTS-1:0]                    [3:0] s_axi_arqos;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] s_axi_aruser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] s_axi_rid;
  logic [N_PORTS-1:0]     [AXI_DATA_WIDTH-1:0] s_axi_rdata;
  logic [N_PORTS-1:0]                    [1:0] s_axi_rresp;
  logic [N_PORTS-1:0]                          s_axi_rvalid;
  logic [N_PORTS-1:0]                          s_axi_rready;
  logic [N_PORTS-1:0]                          s_axi_rlast;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] s_axi_ruser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_awid;
  logic [N_PORTS-1:0] [AXI_EXT_ADDR_WIDTH-1:0] m_axi_awaddr;
  logic [N_PORTS-1:0]                          m_axi_awvalid;
  logic [N_PORTS-1:0]                          m_axi_awready;
  logic [N_PORTS-1:0]                    [7:0] m_axi_awlen;
  logic [N_PORTS-1:0]                    [2:0] m_axi_awsize;
  logic [N_PORTS-1:0]                    [1:0] m_axi_awburst;
  logic [N_PORTS-1:0]                          m_axi_awlock;
  logic [N_PORTS-1:0]                    [2:0] m_axi_awprot;
  logic [N_PORTS-1:0]                    [3:0] m_axi_awcache;
  logic [N_PORTS-1:0]                    [3:0] m_axi_awregion;
  logic [N_PORTS-1:0]                    [3:0] m_axi_awqos;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_awuser;

  logic [N_PORTS-1:0]     [AXI_DATA_WIDTH-1:0] m_axi_wdata;
  logic [N_PORTS-1:0]                          m_axi_wvalid;
  logic [N_PORTS-1:0]                          m_axi_wready;
  logic [N_PORTS-1:0]   [AXI_DATA_WIDTH/8-1:0] m_axi_wstrb;
  logic [N_PORTS-1:0]                          m_axi_wlast;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_wuser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_bid;
  logic [N_PORTS-1:0]                    [1:0] m_axi_bresp;
  logic [N_PORTS-1:0]                          m_axi_bvalid;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_buser;
  logic [N_PORTS-1:0]                          m_axi_bready;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_arid;
  logic [N_PORTS-1:0] [AXI_EXT_ADDR_WIDTH-1:0] m_axi_araddr;
  logic [N_PORTS-1:0]                          m_axi_arvalid;
  logic [N_PORTS-1:0]                          m_axi_arready;
  logic [N_PORTS-1:0]                    [7:0] m_axi_arlen;
  logic [N_PORTS-1:0]                    [2:0] m_axi_arsize;
  logic [N_PORTS-1:0]                    [1:0] m_axi_arburst;
  logic [N_PORTS-1:0]                          m_axi_arlock;
  logic [N_PORTS-1:0]                    [2:0] m_axi_arprot;
  logic [N_PORTS-1:0]                    [3:0] m_axi_arcache;
  logic [N_PORTS-1:0]                    [3:0] m_axi_arregion;
  logic [N_PORTS-1:0]                    [3:0] m_axi_arqos;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_aruser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_rid;
  logic [N_PORTS-1:0]     [AXI_DATA_WIDTH-1:0] m_axi_rdata;
  logic [N_PORTS-1:0]                    [1:0] m_axi_rresp;
  logic [N_PORTS-1:0]                          m_axi_rvalid;
  logic [N_PORTS-1:0]                          m_axi_rready;
  logic [N_PORTS-1:0]                          m_axi_rlast;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_ruser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_acp_awid;
  logic [N_PORTS-1:0] [AXI_EXT_ADDR_WIDTH-1:0] m_axi_acp_awaddr;
  logic [N_PORTS-1:0]                          m_axi_acp_awvalid;
  logic [N_PORTS-1:0]                          m_axi_acp_awready;
  logic [N_PORTS-1:0]                    [7:0] m_axi_acp_awlen;
  logic [N_PORTS-1:0]                    [2:0] m_axi_acp_awsize;
  logic [N_PORTS-1:0]                    [1:0] m_axi_acp_awburst;
  logic [N_PORTS-1:0]                          m_axi_acp_awlock;
  logic [N_PORTS-1:0]                    [2:0] m_axi_acp_awprot;
  logic [N_PORTS-1:0]                    [3:0] m_axi_acp_awcache;
  logic [N_PORTS-1:0]                    [3:0] m_axi_acp_awregion;
  logic [N_PORTS-1:0]                    [3:0] m_axi_acp_awqos;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_acp_awuser;

  logic [N_PORTS-1:0]     [AXI_DATA_WIDTH-1:0] m_axi_acp_wdata;
  logic [N_PORTS-1:0]                          m_axi_acp_wvalid;
  logic [N_PORTS-1:0]                          m_axi_acp_wready;
  logic [N_PORTS-1:0]   [AXI_DATA_WIDTH/8-1:0] m_axi_acp_wstrb;
  logic [N_PORTS-1:0]                          m_axi_acp_wlast;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_acp_wuser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_acp_bid;
  logic [N_PORTS-1:0]                    [1:0] m_axi_acp_bresp;
  logic [N_PORTS-1:0]                          m_axi_acp_bvalid;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_acp_buser;
  logic [N_PORTS-1:0]                          m_axi_acp_bready;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_acp_arid;
  logic [N_PORTS-1:0] [AXI_EXT_ADDR_WIDTH-1:0] m_axi_acp_araddr;
  logic [N_PORTS-1:0]                          m_axi_acp_arvalid;
  logic [N_PORTS-1:0]                          m_axi_acp_arready;
  logic [N_PORTS-1:0]                    [7:0] m_axi_acp_arlen;
  logic [N_PORTS-1:0]                    [2:0] m_axi_acp_arsize;
  logic [N_PORTS-1:0]                    [1:0] m_axi_acp_arburst;
  logic [N_PORTS-1:0]                          m_axi_acp_arlock;
  logic [N_PORTS-1:0]                    [2:0] m_axi_acp_arprot;
  logic [N_PORTS-1:0]                    [3:0] m_axi_acp_arcache;
  logic [N_PORTS-1:0]                    [3:0] m_axi_acp_arregion;
  logic [N_PORTS-1:0]                    [3:0] m_axi_acp_arqos;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_acp_aruser;

  logic [N_PORTS-1:0]       [AXI_ID_WIDTH-1:0] m_axi_acp_rid;
  logic [N_PORTS-1:0]     [AXI_DATA_WIDTH-1:0] m_axi_acp_rdata;
  logic [N_PORTS-1:0]                    [1:0] m_axi_acp_rresp;
  logic [N_PORTS-1:0]                          m_axi_acp_rvalid;
  logic [N_PORTS-1:0]                          m_axi_acp_rready;
  logic [N_PORTS-1:0]                          m_axi_acp_rlast;
  logic [N_PORTS-1:0]     [AXI_USER_WIDTH-1:0] m_axi_acp_ruser;

  logic [N_PORTS-1:0]                          intr_rab_miss;
  logic [N_PORTS-1:0]                          intr_rab_multi;
  logic [N_PORTS-1:0]                          intr_rab_prot;
  logic                                        intr_mhf_full;

  //  █████╗ ███████╗███████╗██╗ ██████╗ ███╗   ██╗███╗   ███╗███████╗███╗   ██╗████████╗███████╗
  // ██╔══██╗██╔════╝██╔════╝██║██╔════╝ ████╗  ██║████╗ ████║██╔════╝████╗  ██║╚══██╔══╝██╔════╝
  // ███████║███████╗███████╗██║██║  ███╗██╔██╗ ██║██╔████╔██║█████╗  ██╔██╗ ██║   ██║   ███████╗
  // ██╔══██║╚════██║╚════██║██║██║   ██║██║╚██╗██║██║╚██╔╝██║██╔══╝  ██║╚██╗██║   ██║   ╚════██║
  // ██║  ██║███████║███████║██║╚██████╔╝██║ ╚████║██║ ╚═╝ ██║███████╗██║ ╚████║   ██║   ███████║
  // ╚═╝  ╚═╝╚══════╝╚══════╝╚═╝ ╚═════╝ ╚═╝  ╚═══╝╚═╝     ╚═╝╚══════╝╚═╝  ╚═══╝   ╚═╝   ╚══════╝
  //
  //------------------------------   *******   ---------------------------------------
  assign s_axi_awid     = {socbus_to_rab.aw_id    };
  assign s_axi_awaddr   = {socbus_to_rab.aw_addr  };
  assign s_axi_awvalid  = {socbus_to_rab.aw_valid };
  assign                  {socbus_to_rab.aw_ready } = s_axi_awready;
  assign s_axi_awlen    = {socbus_to_rab.aw_len   };
  assign s_axi_awsize   = {socbus_to_rab.aw_size  };
  assign s_axi_awburst  = {socbus_to_rab.aw_burst };
  assign s_axi_awlock   = {socbus_to_rab.aw_lock  };
  assign s_axi_awprot   = {socbus_to_rab.aw_prot  };
  assign s_axi_awcache  = {socbus_to_rab.aw_cache };
  assign s_axi_awregion = {socbus_to_rab.aw_region};
  assign s_axi_awqos    = {socbus_to_rab.aw_qos   };
  assign s_axi_awuser   = {socbus_to_rab.aw_user  };

  assign s_axi_wdata    = {socbus_to_rab.w_data   };
  assign s_axi_wvalid   = {socbus_to_rab.w_valid  };
  assign                  {socbus_to_rab.w_ready  } = s_axi_wready;
  assign s_axi_wstrb    = {socbus_to_rab.w_strb   };
  assign s_axi_wlast    = {socbus_to_rab.w_last   };
  assign s_axi_wuser    = {socbus_to_rab.w_user   };

  assign                  {socbus_to_rab.b_id     } = s_axi_bid;
  assign                  {socbus_to_rab.b_resp   } = s_axi_bresp;
  assign                  {socbus_to_rab.b_valid  } = s_axi_bvalid;
  assign                  {socbus_to_rab.b_user   } = s_axi_buser;
  assign s_axi_bready   = {socbus_to_rab.b_ready  };

  assign s_axi_arid     = {socbus_to_rab.ar_id    };
  assign s_axi_araddr   = {socbus_to_rab.ar_addr  };
  assign s_axi_arvalid  = {socbus_to_rab.ar_valid };
  assign                  {socbus_to_rab.ar_ready } = s_axi_arready;
  assign s_axi_arlen    = {socbus_to_rab.ar_len   };
  assign s_axi_arsize   = {socbus_to_rab.ar_size  };
  assign s_axi_arburst  = {socbus_to_rab.ar_burst };
  assign s_axi_arlock   = {socbus_to_rab.ar_lock  };
  assign s_axi_arprot   = {socbus_to_rab.ar_prot  };
  assign s_axi_arcache  = {socbus_to_rab.ar_cache };
  assign s_axi_arregion = {socbus_to_rab.ar_region};
  assign s_axi_arqos    = {socbus_to_rab.ar_qos   };
  assign s_axi_aruser   = {socbus_to_rab.ar_user  };

  assign                  {socbus_to_rab.r_id     } = s_axi_rid;
  assign                  {socbus_to_rab.r_data   } = s_axi_rdata;
  assign                  {socbus_to_rab.r_resp   } = s_axi_rresp;
  assign                  {socbus_to_rab.r_valid  } = s_axi_rvalid;
  assign s_axi_rready   = {socbus_to_rab.r_ready  };
  assign                  {socbus_to_rab.r_last   } = s_axi_rlast;
  assign                  {socbus_to_rab.r_user   } = s_axi_ruser;

  //------------------------------   *******   ---------------------------------------
  assign                 {rab_master.aw_id    } = m_axi_awid;
  assign                 {rab_master.aw_addr  } = m_axi_awaddr;
  assign                 {rab_master.aw_valid } = m_axi_awvalid;
  assign m_axi_awready = {rab_master.aw_ready };
  assign                 {rab_master.aw_len   } = m_axi_awlen;
  assign                 {rab_master.aw_size  } = m_axi_awsize;
  assign                 {rab_master.aw_burst } = m_axi_awburst;
  assign                 {rab_master.aw_lock  } = m_axi_awlock;
  assign                 {rab_master.aw_prot  } = m_axi_awprot;
  assign                 {rab_master.aw_cache } = m_axi_awcache;
  assign                 {rab_master.aw_region} = m_axi_awregion;
  assign                 {rab_master.aw_qos   } = m_axi_awqos;
  assign                 {rab_master.aw_user  } = m_axi_awuser;

  assign                 {rab_master.w_data   } = m_axi_wdata;
  assign                 {rab_master.w_valid  } = m_axi_wvalid;
  assign m_axi_wready  = {rab_master.w_ready  };
  assign                 {rab_master.w_strb   } = m_axi_wstrb;
  assign                 {rab_master.w_last   } = m_axi_wlast;
  assign                 {rab_master.w_user   } = m_axi_wuser;

  assign m_axi_bid     = {rab_master.b_id     };
  assign m_axi_bresp   = {rab_master.b_resp   };
  assign m_axi_bvalid  = {rab_master.b_valid  };
  assign m_axi_buser   = {rab_master.b_user   };
  assign                 {rab_master.b_ready  } = m_axi_bready;

  assign                 {rab_master.ar_id    } = m_axi_arid;
  assign                 {rab_master.ar_addr  } = m_axi_araddr;
  assign                 {rab_master.ar_valid } = m_axi_arvalid;
  assign m_axi_arready = {rab_master.ar_ready };
  assign                 {rab_master.ar_len   } = m_axi_arlen;
  assign                 {rab_master.ar_size  } = m_axi_arsize;
  assign                 {rab_master.ar_burst } = m_axi_arburst;
  assign                 {rab_master.ar_lock  } = m_axi_arlock;
  assign                 {rab_master.ar_prot  } = m_axi_arprot;
  assign                 {rab_master.ar_cache } = m_axi_arcache;
  assign                 {rab_master.ar_region} = m_axi_arregion;
  assign                 {rab_master.ar_qos   } = m_axi_arqos;
  assign                 {rab_master.ar_user  } = m_axi_aruser;

  assign  m_axi_rid    = {rab_master.r_id     };
  assign  m_axi_rdata  = {rab_master.r_data   };
  assign  m_axi_rresp  = {rab_master.r_resp   };
  assign  m_axi_rvalid = {rab_master.r_valid  };
  assign                 {rab_master.r_ready  }  = m_axi_rready;
  assign  m_axi_rlast  = {rab_master.r_last   };
  assign  m_axi_ruser  = {rab_master.r_user   };

  //------------------------------   *******   ---------------------------------------
  assign                     {rab_acp_id_remap.aw_id    } = m_axi_acp_awid;
  assign                     {rab_acp_id_remap.aw_addr  } = m_axi_acp_awaddr;
  assign                     {rab_acp_id_remap.aw_valid } = m_axi_acp_awvalid;
  assign m_axi_acp_awready = {rab_acp_id_remap.aw_ready };
  assign                     {rab_acp_id_remap.aw_len   } = m_axi_acp_awlen;
  assign                     {rab_acp_id_remap.aw_size  } = m_axi_acp_awsize;
  assign                     {rab_acp_id_remap.aw_burst } = m_axi_acp_awburst;
  assign                     {rab_acp_id_remap.aw_lock  } = m_axi_acp_awlock;
  assign                     {rab_acp_id_remap.aw_prot  } = m_axi_acp_awprot;
  // rab_acp_id_remap.aw_cache is set later
  assign                     {rab_acp_id_remap.aw_region} = m_axi_acp_awregion;
  assign                     {rab_acp_id_remap.aw_qos   } = m_axi_acp_awqos;
  assign                     {rab_acp_id_remap.aw_user  } = m_axi_acp_awuser;

  assign                     {rab_acp_id_remap.w_data   } = m_axi_acp_wdata;
  assign                     {rab_acp_id_remap.w_valid  } = m_axi_acp_wvalid;
  assign m_axi_acp_wready  = {rab_acp_id_remap.w_ready  };
  assign                     {rab_acp_id_remap.w_strb   } = m_axi_acp_wstrb;
  assign                     {rab_acp_id_remap.w_last   } = m_axi_acp_wlast;
  assign                     {rab_acp_id_remap.w_user   } = m_axi_acp_wuser;

  assign m_axi_acp_bid     = {rab_acp_id_remap.b_id     };
  assign m_axi_acp_bresp   = {rab_acp_id_remap.b_resp   };
  assign m_axi_acp_bvalid  = {rab_acp_id_remap.b_valid  };
  assign m_axi_acp_buser   = {rab_acp_id_remap.b_user   };
  assign                     {rab_acp_id_remap.b_ready  } = m_axi_acp_bready;

  assign                     {rab_acp_id_remap.ar_id    } = m_axi_acp_arid;
  assign                     {rab_acp_id_remap.ar_addr  } = m_axi_acp_araddr;
  assign                     {rab_acp_id_remap.ar_valid } = m_axi_acp_arvalid;
  assign m_axi_acp_arready = {rab_acp_id_remap.ar_ready };
  assign                     {rab_acp_id_remap.ar_len   } = m_axi_acp_arlen;
  assign                     {rab_acp_id_remap.ar_size  } = m_axi_acp_arsize;
  assign                     {rab_acp_id_remap.ar_burst } = m_axi_acp_arburst;
  assign                     {rab_acp_id_remap.ar_lock  } = m_axi_acp_arlock;
  assign                     {rab_acp_id_remap.ar_prot  } = m_axi_acp_arprot;
  // rab_acp_id_remap.ar_cache is set later
  assign                     {rab_acp_id_remap.ar_user  } = m_axi_acp_aruser;

  assign m_axi_acp_rid     = {rab_acp_id_remap.r_id     };
  assign m_axi_acp_rdata   = {rab_acp_id_remap.r_data   };
  assign m_axi_acp_rresp   = {rab_acp_id_remap.r_resp   };
  assign m_axi_acp_rvalid  = {rab_acp_id_remap.r_valid  };
  assign                     {rab_acp_id_remap.r_ready  } = m_axi_acp_rready;
  assign m_axi_acp_rlast   = {rab_acp_id_remap.r_last   };
  assign m_axi_acp_ruser   = {rab_acp_id_remap.r_user   };

  //------------------------------   *******   ---------------------------------------
  // use caches with Write Back and allocate on Read and Write
  // This tells the PS interconnect to route ACP to cache instead of memory
  // (See AXI Protocol Specification A4.4 Memory Types)
  assign rab_acp_id_remap.aw_cache = 4'b1111;
  assign rab_acp_id_remap.ar_cache = 4'b1111;

  //------------------------------   *******   ---------------------------------------
  assign intr_miss_o     = | intr_rab_miss;
  assign intr_multi_o    = | intr_rab_multi;
  assign intr_prot_o     = | intr_rab_prot;
  assign intr_mhf_full_o = intr_mhf_full;

  //------------------------------   arregion, arqos ---------------------------------
  assign m_axi_arregion = 4'b0;
  assign m_axi_arqos    = 4'b0;

  //  █████╗ ██╗  ██╗██╗    ██████╗  █████╗ ██████╗     ████████╗ ██████╗ ██████╗
  // ██╔══██╗╚██╗██╔╝██║    ██╔══██╗██╔══██╗██╔══██╗    ╚══██╔══╝██╔═══██╗██╔══██╗
  // ███████║ ╚███╔╝ ██║    ██████╔╝███████║██████╔╝       ██║   ██║   ██║██████╔╝
  // ██╔══██║ ██╔██╗ ██║    ██╔══██╗██╔══██║██╔══██╗       ██║   ██║   ██║██╔═══╝
  // ██║  ██║██╔╝ ██╗██║    ██║  ██║██║  ██║██████╔╝       ██║   ╚██████╔╝██║
  // ╚═╝  ╚═╝╚═╝  ╚═╝╚═╝    ╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝        ╚═╝    ╚═════╝ ╚═╝
  //
  axi_rab_top
    #(
      .N_PORTS             ( N_PORTS             ),
      .N_L2_SETS           ( 32                  ),
      .N_L2_SET_ENTRIES    ( 32                  ),
      .AXI_DATA_WIDTH      ( AXI_DATA_WIDTH      ),
      .AXI_S_ADDR_WIDTH    ( AXI_ADDR_WIDTH      ),
      .AXI_M_ADDR_WIDTH    ( AXI_EXT_ADDR_WIDTH  ),
      .AXI_LITE_DATA_WIDTH ( AXI_LITE_DATA_WIDTH ),
      .AXI_LITE_ADDR_WIDTH ( AXI_LITE_ADDR_WIDTH ),
      .AXI_ID_WIDTH        ( AXI_ID_WIDTH        ),
      .AXI_USER_WIDTH      ( AXI_USER_WIDTH      )
      )
  axi_rab_top_i
    (
      .Clk_CI             ( clk_i              ),
      .NonGatedClk_CI     ( clk_i              ),
      .Rst_RBI            ( rst_ni             ),

      .s_axi4_awid        ( s_axi_awid         ),
      .s_axi4_awaddr      ( s_axi_awaddr       ),
      .s_axi4_awvalid     ( s_axi_awvalid      ),
      .s_axi4_awready     ( s_axi_awready      ),
      .s_axi4_awlen       ( s_axi_awlen        ),
      .s_axi4_awsize      ( s_axi_awsize       ),
      .s_axi4_awburst     ( s_axi_awburst      ),
      .s_axi4_awlock      ( s_axi_awlock       ),
      .s_axi4_awprot      ( s_axi_awprot       ),
      .s_axi4_awcache     ( s_axi_awcache      ),
      .s_axi4_awregion    ( s_axi_awregion     ),
      .s_axi4_awqos       ( s_axi_awqos        ),
      .s_axi4_awuser      ( s_axi_awuser       ),

      .s_axi4_wdata       ( s_axi_wdata        ),
      .s_axi4_wvalid      ( s_axi_wvalid       ),
      .s_axi4_wready      ( s_axi_wready       ),
      .s_axi4_wstrb       ( s_axi_wstrb        ),
      .s_axi4_wlast       ( s_axi_wlast        ),
      .s_axi4_wuser       ( s_axi_wuser        ),

      .s_axi4_bid         ( s_axi_bid          ),
      .s_axi4_bresp       ( s_axi_bresp        ),
      .s_axi4_bvalid      ( s_axi_bvalid       ),
      .s_axi4_buser       ( s_axi_buser        ),
      .s_axi4_bready      ( s_axi_bready       ),

      .s_axi4_arid        ( s_axi_arid         ),
      .s_axi4_araddr      ( s_axi_araddr       ),
      .s_axi4_arvalid     ( s_axi_arvalid      ),
      .s_axi4_arready     ( s_axi_arready      ),
      .s_axi4_arlen       ( s_axi_arlen        ),
      .s_axi4_arsize      ( s_axi_arsize       ),
      .s_axi4_arburst     ( s_axi_arburst      ),
      .s_axi4_arlock      ( s_axi_arlock       ),
      .s_axi4_arprot      ( s_axi_arprot       ),
      .s_axi4_arcache     ( s_axi_arcache      ),
      //.s_axi4_arregion    ( s_axi_arregion     ), // not there in axi_rab_top...
      //.s_axi4_arqos       ( s_axi_arqos        ), // not there in axi_rab_top...
      .s_axi4_aruser      ( s_axi_aruser       ),

      .s_axi4_rid         ( s_axi_rid          ),
      .s_axi4_rdata       ( s_axi_rdata        ),
      .s_axi4_rresp       ( s_axi_rresp        ),
      .s_axi4_rvalid      ( s_axi_rvalid       ),
      .s_axi4_rready      ( s_axi_rready       ),
      .s_axi4_rlast       ( s_axi_rlast        ),
      .s_axi4_ruser       ( s_axi_ruser        ),

      .m0_axi4_awid       ( m_axi_awid         ),
      .m0_axi4_awaddr     ( m_axi_awaddr       ),
      .m0_axi4_awvalid    ( m_axi_awvalid      ),
      .m0_axi4_awready    ( m_axi_awready      ),
      .m0_axi4_awlen      ( m_axi_awlen        ),
      .m0_axi4_awsize     ( m_axi_awsize       ),
      .m0_axi4_awburst    ( m_axi_awburst      ),
      .m0_axi4_awlock     ( m_axi_awlock       ),
      .m0_axi4_awprot     ( m_axi_awprot       ),
      .m0_axi4_awcache    ( m_axi_awcache      ),
      .m0_axi4_awregion   ( m_axi_awregion     ),
      .m0_axi4_awqos      ( m_axi_awqos        ),
      .m0_axi4_awuser     ( m_axi_awuser       ),

      .m0_axi4_wdata      ( m_axi_wdata        ),
      .m0_axi4_wvalid     ( m_axi_wvalid       ),
      .m0_axi4_wready     ( m_axi_wready       ),
      .m0_axi4_wstrb      ( m_axi_wstrb        ),
      .m0_axi4_wlast      ( m_axi_wlast        ),
      .m0_axi4_wuser      ( m_axi_wuser        ),

      .m0_axi4_bid        ( m_axi_bid          ),
      .m0_axi4_bresp      ( m_axi_bresp        ),
      .m0_axi4_bvalid     ( m_axi_bvalid       ),
      .m0_axi4_buser      ( m_axi_buser        ),
      .m0_axi4_bready     ( m_axi_bready       ),

      .m0_axi4_arid       ( m_axi_arid         ),
      .m0_axi4_araddr     ( m_axi_araddr       ),
      .m0_axi4_arvalid    ( m_axi_arvalid      ),
      .m0_axi4_arready    ( m_axi_arready      ),
      .m0_axi4_arlen      ( m_axi_arlen        ),
      .m0_axi4_arsize     ( m_axi_arsize       ),
      .m0_axi4_arburst    ( m_axi_arburst      ),
      .m0_axi4_arlock     ( m_axi_arlock       ),
      .m0_axi4_arprot     ( m_axi_arprot       ),
      .m0_axi4_arcache    ( m_axi_arcache      ),
      //.m0_axi4_arregion   ( m_axi_arregion     ), // not there in axi_rab_top...
      //.m0_axi4_arqos      ( m_axi_arqos        ), // not there in axi_rab_top...
      .m0_axi4_aruser     ( m_axi_aruser       ),

      .m0_axi4_rid        ( m_axi_rid          ),
      .m0_axi4_rdata      ( m_axi_rdata        ),
      .m0_axi4_rresp      ( m_axi_rresp        ),
      .m0_axi4_rvalid     ( m_axi_rvalid       ),
      .m0_axi4_rready     ( m_axi_rready       ),
      .m0_axi4_rlast      ( m_axi_rlast        ),
      .m0_axi4_ruser      ( m_axi_ruser        ),

      .m1_axi4_awid       ( m_axi_acp_awid     ),
      .m1_axi4_awaddr     ( m_axi_acp_awaddr   ),
      .m1_axi4_awvalid    ( m_axi_acp_awvalid  ),
      .m1_axi4_awready    ( m_axi_acp_awready  ),
      .m1_axi4_awlen      ( m_axi_acp_awlen    ),
      .m1_axi4_awsize     ( m_axi_acp_awsize   ),
      .m1_axi4_awburst    ( m_axi_acp_awburst  ),
      .m1_axi4_awlock     ( m_axi_acp_awlock   ),
      .m1_axi4_awprot     ( m_axi_acp_awprot   ),
      .m1_axi4_awcache    ( m_axi_acp_awcache  ),
      .m1_axi4_awregion   ( m_axi_acp_awregion ),
      .m1_axi4_awqos      ( m_axi_acp_awqos    ),
      .m1_axi4_awuser     ( m_axi_acp_awuser   ),

      .m1_axi4_wdata      ( m_axi_acp_wdata    ),
      .m1_axi4_wvalid     ( m_axi_acp_wvalid   ),
      .m1_axi4_wready     ( m_axi_acp_wready   ),
      .m1_axi4_wstrb      ( m_axi_acp_wstrb    ),
      .m1_axi4_wlast      ( m_axi_acp_wlast    ),
      .m1_axi4_wuser      ( m_axi_acp_wuser    ),

      .m1_axi4_bid        ( m_axi_acp_bid      ),
      .m1_axi4_bresp      ( m_axi_acp_bresp    ),
      .m1_axi4_bvalid     ( m_axi_acp_bvalid   ),
      .m1_axi4_buser      ( m_axi_acp_buser    ),
      .m1_axi4_bready     ( m_axi_acp_bready   ),

      .m1_axi4_arid       ( m_axi_acp_arid     ),
      .m1_axi4_araddr     ( m_axi_acp_araddr   ),
      .m1_axi4_arvalid    ( m_axi_acp_arvalid  ),
      .m1_axi4_arready    ( m_axi_acp_arready  ),
      .m1_axi4_arlen      ( m_axi_acp_arlen    ),
      .m1_axi4_arsize     ( m_axi_acp_arsize   ),
      .m1_axi4_arburst    ( m_axi_acp_arburst  ),
      .m1_axi4_arlock     ( m_axi_acp_arlock   ),
      .m1_axi4_arprot     ( m_axi_acp_arprot   ),
      .m1_axi4_arcache    ( m_axi_acp_arcache  ),
      //.m1_axi4_arregion   ( m_axi_acp_arregion ), // not there in axi_rab_top...
      //.m1_axi4_arqos      ( m_axi_acp_arqos    ), // not there in axi_rab_top...
      .m1_axi4_aruser     ( m_axi_acp_aruser   ),

      .m1_axi4_rid        ( m_axi_acp_rid      ),
      .m1_axi4_rdata      ( m_axi_acp_rdata    ),
      .m1_axi4_rresp      ( m_axi_acp_rresp    ),
      .m1_axi4_rvalid     ( m_axi_acp_rvalid   ),
      .m1_axi4_rready     ( m_axi_acp_rready   ),
      .m1_axi4_rlast      ( m_axi_acp_rlast    ),
      .m1_axi4_ruser      ( m_axi_acp_ruser    ),

      .s_axi4lite_awaddr  ( rab_lite.aw_addr   ),
      .s_axi4lite_awvalid ( rab_lite.aw_valid  ),
      .s_axi4lite_awready ( rab_lite.aw_ready  ),

      .s_axi4lite_wdata   ( rab_lite.w_data    ),
      .s_axi4lite_wvalid  ( rab_lite.w_valid   ),
      .s_axi4lite_wready  ( rab_lite.w_ready   ),
      .s_axi4lite_wstrb   ( rab_lite.w_strb    ),

      .s_axi4lite_bresp   ( rab_lite.b_resp    ),
      .s_axi4lite_bvalid  ( rab_lite.b_valid   ),
      .s_axi4lite_bready  ( rab_lite.b_ready   ),

      .s_axi4lite_araddr  ( rab_lite.ar_addr   ),
      .s_axi4lite_arvalid ( rab_lite.ar_valid  ),
      .s_axi4lite_arready ( rab_lite.ar_ready  ),

      .s_axi4lite_rdata   ( rab_lite.r_data    ),
      .s_axi4lite_rresp   ( rab_lite.r_resp    ),
      .s_axi4lite_rvalid  ( rab_lite.r_valid   ),
      .s_axi4lite_rready  ( rab_lite.r_ready   ),

      .int_miss           ( intr_rab_miss      ),
      .int_multi          ( intr_rab_multi     ),
      .int_prot           ( intr_rab_prot      ),
      .int_mhf_full       ( intr_mhf_full      )
    );

endmodule
