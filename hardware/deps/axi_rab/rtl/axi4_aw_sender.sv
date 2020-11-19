// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi4_aw_sender #(
  parameter AXI_ADDR_WIDTH  = 40,
  parameter AXI_ID_WIDTH    = 4,
  parameter AXI_USER_WIDTH  = 4,
  parameter ENABLE_L2TLB    = 0,
  localparam type addr_t = logic [AXI_ADDR_WIDTH-1:0],
  localparam type id_t = logic [AXI_ID_WIDTH-1:0],
  localparam type user_t = logic [AXI_USER_WIDTH-1:0]
) (
  input  logic              axi4_aclk,
  input  logic              axi4_arstn,

  output logic              l1_done_o,
  input  logic              l1_accept_i,
  input  logic              l1_drop_i,
  input  logic              l1_save_i,

  output logic              l2_done_o,
  input  logic              l2_accept_i,
  input  logic              l2_drop_i,
  output logic              l2_sending_o,

  input  addr_t             l1_awaddr_i,
  input  addr_t             l2_awaddr_i,

  input  id_t               s_axi4_awid,
  input  logic              s_axi4_awvalid,
  output logic              s_axi4_awready,
  input  axi_pkg::len_t     s_axi4_awlen,
  input  axi_pkg::size_t    s_axi4_awsize,
  input  axi_pkg::burst_t   s_axi4_awburst,
  input  logic              s_axi4_awlock,
  input  axi_pkg::prot_t    s_axi4_awprot,
  input  axi_pkg::atop_t    s_axi4_awatop,
  input  axi_pkg::cache_t   s_axi4_awcache,
  input  axi_pkg::region_t  s_axi4_awregion,
  input  axi_pkg::qos_t     s_axi4_awqos,
  input  user_t             s_axi4_awuser,

  output id_t               m_axi4_awid,
  output addr_t             m_axi4_awaddr,
  output logic              m_axi4_awvalid,
  input  logic              m_axi4_awready,
  output axi_pkg::len_t     m_axi4_awlen,
  output axi_pkg::size_t    m_axi4_awsize,
  output axi_pkg::burst_t   m_axi4_awburst,
  output logic              m_axi4_awlock,
  output axi_pkg::prot_t    m_axi4_awprot,
  output axi_pkg::atop_t    m_axi4_awatop,
  output axi_pkg::cache_t   m_axi4_awcache,
  output axi_pkg::region_t  m_axi4_awregion,
  output axi_pkg::qos_t     m_axi4_awqos,
  output user_t             m_axi4_awuser
);

  logic l1_save;

  logic l2_sent;
  logic l2_available_q;

  assign l1_save    = l1_save_i & l2_available_q;

  assign l1_done_o  = s_axi4_awvalid & s_axi4_awready ;

  // if 1: accept and forward a transaction translated by L1
  //    2: drop or save request (if L2 slot not occupied already)
  assign m_axi4_awvalid = (s_axi4_awvalid & l1_accept_i) |
                          l2_sending_o;
  assign s_axi4_awready = (m_axi4_awvalid & m_axi4_awready & ~l2_sending_o) |
                          (s_axi4_awvalid & (l1_drop_i | l1_save));

  if (ENABLE_L2TLB) begin : gen_l2_tlb
    user_t            l2_axi4_awuser;
    axi_pkg::cache_t  l2_axi4_awcache;
    axi_pkg::region_t l2_axi4_awregion;
    axi_pkg::qos_t    l2_axi4_awqos;
    axi_pkg::prot_t   l2_axi4_awprot;
    axi_pkg::atop_t   l2_axi4_awatop;
    logic             l2_axi4_awlock;
    axi_pkg::burst_t  l2_axi4_awburst;
    axi_pkg::size_t   l2_axi4_awsize;
    axi_pkg::len_t    l2_axi4_awlen;
    id_t              l2_axi4_awid;

    assign m_axi4_awuser   = l2_sending_o ? l2_axi4_awuser   : s_axi4_awuser;
    assign m_axi4_awcache  = l2_sending_o ? l2_axi4_awcache  : s_axi4_awcache;
    assign m_axi4_awregion = l2_sending_o ? l2_axi4_awregion : s_axi4_awregion;
    assign m_axi4_awqos    = l2_sending_o ? l2_axi4_awqos    : s_axi4_awqos;
    assign m_axi4_awprot   = l2_sending_o ? l2_axi4_awprot   : s_axi4_awprot;
    assign m_axi4_awatop   = l2_sending_o ? l2_axi4_awatop   : s_axi4_awatop;
    assign m_axi4_awlock   = l2_sending_o ? l2_axi4_awlock   : s_axi4_awlock;
    assign m_axi4_awburst  = l2_sending_o ? l2_axi4_awburst  : s_axi4_awburst;
    assign m_axi4_awsize   = l2_sending_o ? l2_axi4_awsize   : s_axi4_awsize;
    assign m_axi4_awlen    = l2_sending_o ? l2_axi4_awlen    : s_axi4_awlen;
    assign m_axi4_awaddr   = l2_sending_o ? l2_awaddr_i      : l1_awaddr_i;
    assign m_axi4_awid     = l2_sending_o ? l2_axi4_awid     : s_axi4_awid;

    // buffer AXI signals in case of L1 miss
    always @(posedge axi4_aclk, negedge axi4_arstn) begin
      if (!axi4_arstn) begin
        l2_axi4_awuser   <=  'b0;
        l2_axi4_awcache  <=  'b0;
        l2_axi4_awregion <=  'b0;
        l2_axi4_awqos    <=  'b0;
        l2_axi4_awprot   <=  'b0;
        l2_axi4_awatop   <=  'b0;
        l2_axi4_awlock   <= 1'b0;
        l2_axi4_awburst  <=  'b0;
        l2_axi4_awsize   <=  'b0;
        l2_axi4_awlen    <=  'b0;
        l2_axi4_awid     <=  'b0;
      end else if (l1_save) begin
        l2_axi4_awuser   <= s_axi4_awuser;
        l2_axi4_awcache  <= s_axi4_awcache;
        l2_axi4_awregion <= s_axi4_awregion;
        l2_axi4_awqos    <= s_axi4_awqos;
        l2_axi4_awprot   <= s_axi4_awprot;
        l2_axi4_awatop   <= s_axi4_awatop;
        l2_axi4_awlock   <= s_axi4_awlock;
        l2_axi4_awburst  <= s_axi4_awburst;
        l2_axi4_awsize   <= s_axi4_awsize;
        l2_axi4_awlen    <= s_axi4_awlen;
        l2_axi4_awid     <= s_axi4_awid;
      end
    end

    // signal that an l1_save_i can be accepted
    always @(posedge axi4_aclk, negedge axi4_arstn) begin
      if (!axi4_arstn ) begin
        l2_available_q <= 1'b1;
      end else if (l2_sent || l2_drop_i) begin
        l2_available_q <= 1'b1;
      end else if (l1_save) begin
        l2_available_q <= 1'b0;
      end
    end

    assign l2_sending_o = l2_accept_i & ~l2_available_q;
    assign l2_sent      = l2_sending_o & m_axi4_awvalid & m_axi4_awready;

    // if 1: having sent out a transaction translated by L2
    //    2: drop request (L2 slot is available again)
    assign l2_done_o    = l2_sent | l2_drop_i;

  end else begin : gen_no_l2_tlb
    assign m_axi4_awuser   =  s_axi4_awuser;
    assign m_axi4_awcache  =  s_axi4_awcache;
    assign m_axi4_awregion =  s_axi4_awregion;
    assign m_axi4_awqos    =  s_axi4_awqos;
    assign m_axi4_awprot   =  s_axi4_awprot;
    assign m_axi4_awatop   =  s_axi4_awatop;
    assign m_axi4_awlock   =  s_axi4_awlock;
    assign m_axi4_awburst  =  s_axi4_awburst;
    assign m_axi4_awsize   =  s_axi4_awsize;
    assign m_axi4_awlen    =  s_axi4_awlen;
    assign m_axi4_awaddr   =  l1_awaddr_i;
    assign m_axi4_awid     =  s_axi4_awid;

    assign l2_sending_o    = 1'b0;
    assign l2_available_q  = 1'b0;
    assign l2_done_o       = 1'b0;
  end

endmodule
