// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "axi/assign.svh"
`include "common_cells/registers.svh"

module mempool_system
  import mempool_pkg::*;
#(
  // TCDM
  parameter addr_t       TCDMBaseAddr  = 32'h0000_0000,
  // Boot address
  parameter addr_t       BootAddr      = 32'h0000_0000
) (
  input logic                clk_i,
  input logic                rst_ni,

  input  logic               fetch_en_i,
  output logic               eoc_valid_o,
  output logic               busy_o,

  output axi_system_req_t    mst_req_o,
  input  axi_system_resp_t   mst_resp_i,

  input  axi_system_req_t    slv_req_i,
  output axi_system_resp_t   slv_resp_o
);

  import axi_pkg::xbar_cfg_t;
  import axi_pkg::xbar_rule_32_t;

  `include "reqrsp_interface/typedef.svh"

  /*********
   *  AXI  *
   *********/

  // Overview of AXI buses with SRAM L2
  //
  //      mst_demux
  //        / |
  //       /  | soc  +----------+ periph  +---------+
  //      |  0|=====>| soc_xbar |========>| periph  |
  //  mst |   |      +----------+         +---------+
  // ====>|   |
  //      |   | l2   +----------+  mem    +---------+ bank  +--------+
  //      |  1|=====>| axi2mem  |-------->| l2_xbar |------>| l2_mem |
  //       \  |      +----------+         +---------+       +--------+
  //        \_|
  //                  == axi ==>          -- tcdm -->
  //
  // Overview of AXI buses with DRAM L2
  //
  //      mst_demux
  //        / |
  //       /  | soc  +----------+ periph  +---------+
  //      |  0|=====>| soc_xbar |========>| periph  |
  //  mst |   |      +----------+         +---------+
  // ====>|   |
  //      |   | l2   +----------+  mem_one_port  +--------------+
  //      |  1|=====>| AXI_Mux  |===============>| AXI Port Out |
  //       \  |      +----------+                +--------------+
  //        \_|
  //                  == axi ==>

  localparam NumAXIMasters = NumSystemXbarMasters;
  localparam NumAXISlaves  = 3; // control regs, bootrom and the external mst ports
  localparam NumSoCRules   = NumAXISlaves - 1;

  typedef enum logic [$clog2(NumAXISlaves) - 1:0] {
    Peripherals,
    Bootrom,
    External
  } axi_soc_xbar_slave_target;

  typedef enum logic {
    SoCXBar = 0,
    L2Memory = 1
  } axi_mst_demux_slave_target;

  axi_tile_req_t    [NumAXIMasters-1:0] axi_mst_req;
  axi_tile_resp_t   [NumAXIMasters-1:0] axi_mst_resp;
  axi_tile_req_t    [NumAXIMasters-1:0] axi_l2_req;
  axi_tile_resp_t   [NumAXIMasters-1:0] axi_l2_resp;
  axi_tile_req_t    [NumAXIMasters-1:0] axi_soc_req;
  axi_tile_resp_t   [NumAXIMasters-1:0] axi_soc_resp;
  axi_system_req_t  [NumAXISlaves-1:0]  axi_periph_req;
  axi_system_resp_t [NumAXISlaves-1:0]  axi_periph_resp;
  logic             [NumCores-1:0]      wake_up;
  logic             [DataWidth-1:0]     eoc;
  ro_cache_ctrl_t                       ro_cache_ctrl;

  dma_req_t  dma_req;
  logic      dma_req_valid;
  logic      dma_req_ready;
  dma_meta_t dma_meta;
  logic      [1-1:0] dma_id;

  localparam xbar_cfg_t MstDemuxCfg = '{
    NoSlvPorts         : 1, // Each master has a private demux
    NoMstPorts         : 2, // going to either the xbar or L2
    MaxMstTrans        : 8,
    MaxSlvTrans        : 4,
    FallThrough        : 1'b0,
    LatencyMode        : axi_pkg::NO_LATENCY,
    PipelineStages     : 0,
    AxiIdWidthSlvPorts : AxiTileIdWidth,
    AxiIdUsedSlvPorts  : AxiTileIdWidth,
    UniqueIds          : 0,
    AxiAddrWidth       : AddrWidth,
    AxiDataWidth       : AxiDataWidth,
    NoAddrRules        : 1
  };

  localparam xbar_cfg_t SoCXBarCfg = '{
    NoSlvPorts         : NumAXIMasters,
    NoMstPorts         : NumAXISlaves,
    MaxMstTrans        : 4,
    MaxSlvTrans        : 4,
    FallThrough        : 1'b0,
    LatencyMode        : axi_pkg::CUT_MST_PORTS,
    PipelineStages     : 0,
    AxiIdWidthSlvPorts : AxiTileIdWidth,
    AxiIdUsedSlvPorts  : AxiTileIdWidth,
    UniqueIds          : 0,
    AxiAddrWidth       : AddrWidth,
    AxiDataWidth       : AxiDataWidth,
    NoAddrRules        : NumSoCRules
  };

  /*********************
   *  MemPool Cluster  *
   ********************/

  mempool_cluster #(
    .TCDMBaseAddr(TCDMBaseAddr),
    .BootAddr    (BootAddr    )
  ) i_mempool_cluster (
    .clk_i          (clk_i                          ),
    .rst_ni         (rst_ni                         ),
    .wake_up_i      (wake_up                        ),
    .testmode_i     (1'b0                           ),
    .scan_enable_i  (1'b0                           ),
    .scan_data_i    (1'b0                           ),
    .scan_data_o    (/* Unused */                   ),
    .ro_cache_ctrl_i(ro_cache_ctrl                  ),
    .dma_req_i      (dma_req                        ),
    .dma_req_valid_i(dma_req_valid                  ),
    .dma_req_ready_o(dma_req_ready                  ),
    .dma_meta_o     (dma_meta                       ),
    .axi_mst_req_o  (axi_mst_req[NumAXIMasters-2:0] ),
    .axi_mst_resp_i (axi_mst_resp[NumAXIMasters-2:0])
  );

  /**********************
   *  AXI Interconnect  *
   **********************/

  localparam addr_t PeripheralsBaseAddr   = 32'h4000_0000;
  localparam addr_t PeripheralsEndAddr    = 32'h4002_0000;
  localparam addr_t L2MemoryBaseAddr      = `ifdef L2_BASE `L2_BASE `else 32'h8000_0000 `endif;
  localparam addr_t L2MemoryEndAddr       = L2MemoryBaseAddr + L2Size;
  localparam addr_t BootromBaseAddr       = 32'hA000_0000;
  localparam addr_t BootromEndAddr        = 32'hA000_FFFF;

  xbar_rule_32_t [            0:0]  mst_demux_rules;
  xbar_rule_32_t [NumSoCRules-1:0] soc_xbar_rules;
  assign mst_demux_rules = '{
    '{idx: L2Memory, start_addr: L2MemoryBaseAddr, end_addr: L2MemoryEndAddr}
  };
  assign soc_xbar_rules = '{
    '{idx: Peripherals, start_addr: PeripheralsBaseAddr, end_addr: PeripheralsEndAddr},
    '{idx: Bootrom, start_addr: BootromBaseAddr, end_addr: BootromEndAddr}
  };

  for (genvar i = 0; i < NumAXIMasters; i++) begin : gen_mst_demux
    axi_xbar #(
      .Cfg          (MstDemuxCfg      ),
      .slv_aw_chan_t(axi_tile_aw_t    ),
      .mst_aw_chan_t(axi_tile_aw_t    ),
      .w_chan_t     (axi_tile_w_t     ),
      .slv_b_chan_t (axi_tile_b_t     ),
      .mst_b_chan_t (axi_tile_b_t     ),
      .slv_ar_chan_t(axi_tile_ar_t    ),
      .mst_ar_chan_t(axi_tile_ar_t    ),
      .slv_r_chan_t (axi_tile_r_t     ),
      .mst_r_chan_t (axi_tile_r_t     ),
      .slv_req_t    (axi_tile_req_t   ),
      .slv_resp_t   (axi_tile_resp_t  ),
      .mst_req_t    (axi_tile_req_t   ),
      .mst_resp_t   (axi_tile_resp_t  ),
      .rule_t       (xbar_rule_32_t   )
    ) i_mst_demux (
      .clk_i                (clk_i                           ),
      .rst_ni               (rst_ni                          ),
      .test_i               (1'b0                            ),
      .slv_ports_req_i      (axi_mst_req[i]                  ),
      .slv_ports_resp_o     (axi_mst_resp[i]                 ),
      .mst_ports_req_o      ({axi_l2_req[i] ,axi_soc_req[i] }),
      .mst_ports_resp_i     ({axi_l2_resp[i],axi_soc_resp[i]}),
      .addr_map_i           (mst_demux_rules                 ),
      .en_default_mst_port_i(1'b1                            ),
      .default_mst_port_i   (SoCXBar                         )
    );
  end

  axi_xbar #(
    .Cfg          (SoCXBarCfg       ),
    .slv_aw_chan_t(axi_tile_aw_t    ),
    .mst_aw_chan_t(axi_system_aw_t  ),
    .w_chan_t     (axi_tile_w_t     ),
    .slv_b_chan_t (axi_tile_b_t     ),
    .mst_b_chan_t (axi_system_b_t   ),
    .slv_ar_chan_t(axi_tile_ar_t    ),
    .mst_ar_chan_t(axi_system_ar_t  ),
    .slv_r_chan_t (axi_tile_r_t     ),
    .mst_r_chan_t (axi_system_r_t   ),
    .slv_req_t    (axi_tile_req_t   ),
    .slv_resp_t   (axi_tile_resp_t  ),
    .mst_req_t    (axi_system_req_t ),
    .mst_resp_t   (axi_system_resp_t),
    .rule_t       (xbar_rule_32_t   )
  ) i_soc_xbar (
    .clk_i                (clk_i                    ),
    .rst_ni               (rst_ni                   ),
    .test_i               (1'b0                     ),
    .slv_ports_req_i      (axi_soc_req              ),
    .slv_ports_resp_o     (axi_soc_resp             ),
    .mst_ports_req_o      (axi_periph_req           ),
    .mst_ports_resp_i     (axi_periph_resp          ),
    .addr_map_i           (soc_xbar_rules           ),
    .en_default_mst_port_i({NumAXIMasters{1'b1}}    ), // default all slave ports to master port External
    .default_mst_port_i   ({NumAXIMasters{External}})
  );

`ifndef DRAM

  /*************
   *  L2 SRAM  *
   *************/

  `REQRSP_TYPEDEF_ALL(axi_to_l2, addr_t, axi_data_t, axi_strb_t)
  typedef logic [L2BankAddrWidth-1:0] l2_bank_addr_t;
  // Axi2ReqRsp
  axi_to_l2_req_t [NumAXIMasters-1:0] axi_to_l2_req;
  axi_to_l2_rsp_t [NumAXIMasters-1:0] axi_to_l2_rsp;
  // Axi2ReqRsp unpacked
  localparam int unsigned NumAXIMastersWidth = (NumAXIMasters > 32'd1) ? unsigned'($clog2(NumAXIMasters)) : 32'd1;
  localparam int unsigned NumL2BanksWidth = (NumL2Banks > 32'd1) ? unsigned'($clog2(NumL2Banks)) : 32'd1;
  typedef logic [NumAXIMastersWidth-1:0] l2_axi_idx_t;
  typedef logic [NumL2BanksWidth-1:0] l2_bank_idx_t;
  axi_to_l2_req_chan_t [NumAXIMasters-1:0] axi_to_l2_req_chan;
  axi_to_l2_rsp_chan_t [NumAXIMasters-1:0] axi_to_l2_rsp_chan;
  logic                [NumAXIMasters-1:0] axi_to_l2_q_valid;
  logic                [NumAXIMasters-1:0] axi_to_l2_q_ready;
  l2_bank_idx_t        [NumAXIMasters-1:0] axi_to_l2_q_sel;
  l2_axi_idx_t         [NumL2Banks-1:0] axi_to_l2_q_idx;
  logic                [NumAXIMasters-1:0] axi_to_l2_p_valid;
  logic                [NumAXIMasters-1:0] axi_to_l2_p_ready;
  l2_axi_idx_t         [NumL2Banks-1:0] axi_to_l2_p_sel;
  // Axi2ReqRsp to bank_adapter
  axi_to_l2_req_chan_t [NumL2Banks-1:0] mem_req_chan;
  axi_to_l2_rsp_chan_t [NumL2Banks-1:0] mem_rsp_chan;
  logic [NumL2Banks-1:0] mem_req_valid;
  logic [NumL2Banks-1:0] mem_req_ready;
  logic [NumL2Banks-1:0] mem_rsp_valid;
  logic [NumL2Banks-1:0] mem_rsp_ready;
  // bank_adapter to banks
  logic          [NumL2Banks-1:0] bank_req;
  logic          [NumL2Banks-1:0] bank_we;
  l2_bank_addr_t [NumL2Banks-1:0] bank_addr;
  axi_data_t     [NumL2Banks-1:0] bank_wdata;
  axi_strb_t     [NumL2Banks-1:0] bank_strb;
  axi_data_t     [NumL2Banks-1:0] bank_rdata;

  for (genvar i = 0; i < NumAXIMasters; i++) begin : gen_l2_adapters
    axi_to_reqrsp #(
      .axi_req_t    (axi_tile_req_t ),
      .axi_rsp_t    (axi_tile_resp_t),
      .AddrWidth    (L2AddrWidth    ),
      .DataWidth    (AxiDataWidth   ),
      .IdWidth      (AxiTileIdWidth ),
      .BufDepth     (3              ),
      .reqrsp_req_t (axi_to_l2_req_t),
      .reqrsp_rsp_t (axi_to_l2_rsp_t)
    ) i_axi_to_reqrsp (
      .clk_i        (clk_i           ),
      .rst_ni       (rst_ni          ),
      .busy_o       (/*unused*/      ),
      .axi_req_i    (axi_l2_req[i]   ),
      .axi_rsp_o    (axi_l2_resp[i]  ),
      .reqrsp_req_o (axi_to_l2_req[i]),
      .reqrsp_rsp_i (axi_to_l2_rsp[i])
    );
    // Repack the structs for the xbar
    assign axi_to_l2_req_chan[i]    = axi_to_l2_req[i].q;
    assign axi_to_l2_q_valid[i]     = axi_to_l2_req[i].q_valid;
    assign axi_to_l2_rsp[i].q_ready = axi_to_l2_q_ready[i];
    assign axi_to_l2_rsp[i].p       = axi_to_l2_rsp_chan[i];
    assign axi_to_l2_rsp[i].p_valid = axi_to_l2_p_valid[i];
    assign axi_to_l2_p_ready[i]     = axi_to_l2_req[i].p_ready;
    // Generate the selection signal
    assign axi_to_l2_q_sel[i] = axi_to_l2_req_chan[i].addr[$clog2(L2BankBeWidth)+:NumL2BanksWidth];
  end

  stream_xbar #(
    .NumInp      (NumAXIMasters       ),
    .NumOut      (NumL2Banks          ),
    .payload_t   (axi_to_l2_req_chan_t),
    .OutSpillReg (1'b1                ),
    .ExtPrio     (1'b0                ),
    .AxiVldRdy   (1'b1                ),
    .LockIn      (1'b1                )
  ) i_l2_req_xbar (
    .clk_i   (clk_i             ),
    .rst_ni  (rst_ni            ),
    .flush_i (1'b0              ),
    .rr_i    ('0                ),
    .data_i  (axi_to_l2_req_chan),
    .sel_i   (axi_to_l2_q_sel   ),
    .valid_i (axi_to_l2_q_valid ),
    .ready_o (axi_to_l2_q_ready ),
    .data_o  (mem_req_chan      ),
    .idx_o   (axi_to_l2_q_idx   ),
    .valid_o (mem_req_valid     ),
    .ready_i (mem_req_ready     )
  );

  stream_xbar #(
    .NumInp      (NumL2Banks          ),
    .NumOut      (NumAXIMasters       ),
    .payload_t   (axi_to_l2_rsp_chan_t),
    .OutSpillReg (1'b0                ),
    .ExtPrio     (1'b0                ),
    .AxiVldRdy   (1'b1                ),
    .LockIn      (1'b1                )
  ) i_l2_rsp_xbar (
    .clk_i   (clk_i             ),
    .rst_ni  (rst_ni            ),
    .flush_i (1'b0              ),
    .rr_i    ('0                ),
    .data_i  (mem_rsp_chan      ),
    .sel_i   (axi_to_l2_p_sel   ),
    .valid_i (mem_rsp_valid     ),
    .ready_o (mem_rsp_ready     ),
    .data_o  (axi_to_l2_rsp_chan),
    .idx_o   (/*unused*/        ),
    .valid_o (axi_to_l2_p_valid ),
    .ready_i (axi_to_l2_p_ready )
  );

  // The initialization at reset is not supported by Verilator. Therefore, we disable the SimInit at
  // reset for Verilator. Since our preloading through the SystemVerilog testbench requires the
  // SimInit value to be assigned at reset, we use the "custom" string to invoke the initialization
  // without setting the memory to known values like "ones" or "zeros".
  localparam L2SimInit = `ifdef VERILATOR "none" `else "custom" `endif;
  localparam L2BankAddrIndex = $clog2(L2BankBeWidth)+$clog2(NumL2Banks);
  for (genvar i = 0; i < NumL2Banks; i++) begin : gen_l2_banks
    tcdm_adapter #(
      .AddrWidth  (L2BankAddrWidth ),
      .DataWidth  (L2BankWidth     ),
      .metadata_t (l2_axi_idx_t    ),
      .LrScEnable (1'b0            ),
      .RegisterAmo(1'b0            )
    ) i_bank_adapter (
      .clk_i       (clk_i                                                 ),
      .rst_ni      (rst_ni                                                ),
      .in_valid_i  (mem_req_valid[i]                                      ),
      .in_ready_o  (mem_req_ready[i]                                      ),
      .in_address_i(mem_req_chan[i].addr[L2BankAddrIndex+:L2BankAddrWidth]),
      .in_amo_i    (mem_req_chan[i].amo                                   ),
      .in_write_i  (mem_req_chan[i].write                                 ),
      .in_wdata_i  (mem_req_chan[i].data                                  ),
      .in_meta_i   (axi_to_l2_q_idx[i]                                    ),
      .in_be_i     (mem_req_chan[i].strb                                  ),
      .in_valid_o  (mem_rsp_valid[i]                                      ),
      .in_ready_i  (mem_rsp_ready[i]                                      ),
      .in_rdata_o  (mem_rsp_chan[i].data                                  ),
      .in_meta_o   (axi_to_l2_p_sel[i]                                    ),
      .out_req_o   (bank_req[i]                                           ),
      .out_add_o   (bank_addr[i]                                          ),
      .out_write_o (bank_we[i]                                            ),
      .out_wdata_o (bank_wdata[i]                                         ),
      .out_be_o    (bank_strb[i]                                          ),
      .out_rdata_i (bank_rdata[i]                                         )
    );
    assign mem_rsp_chan[i].error = 1'b0;

    tc_sram #(
      .DataWidth(L2BankWidth   ),
      .NumWords (L2BankNumWords),
      .NumPorts (1             ),
      .SimInit  (L2SimInit     )
    ) l2_mem (
      .clk_i  (clk_i        ),
      .rst_ni (rst_ni       ),
      .req_i  (bank_req[i]  ),
      .we_i   (bank_we[i]   ),
      .addr_i (bank_addr[i] ),
      .wdata_i(bank_wdata[i]),
      .be_i   (bank_strb[i] ),
      .rdata_o(bank_rdata[i])
    );
  end

`else

  /*************
   *  L2 DRAM  *
   *************/

  // AXI xbar to form one port to DRAM
  localparam NumDramRules = NumDrams;

  xbar_rule_32_t    [NumDramRules-1:0] dram_xbar_rules;
  axi_system_req_t  [NumDrams-1:0]     dram_req_interleaved;
  axi_system_req_t  [NumDrams-1:0]     dram_req;
  axi_system_resp_t [NumDrams-1:0]     dram_resp;

  // AXI brust splitter for DRAM interleaving
  axi_tile_req_t  [NumAXIMasters-1:0] axi_l2_req_splitted;
  axi_tile_resp_t [NumAXIMasters-1:0] axi_l2_resp_splitted;
  axi_tile_req_t  [NumAXIMasters-1:0] axi_l2_req_interleaved;

  generate
    if (DmaBrustLen > Interleave) begin : gen_axi_splitter
      for (genvar i = 0; unsigned'(i) < NumAXIMasters; i++) begin: brust_splitter
        axi_burst_splitter #(
          .MaxReadTxns (16             ),
          .MaxWriteTxns(16             ),
          .AddrWidth   (AddrWidth      ),
          .DataWidth   (AxiDataWidth   ),
          .IdWidth     (AxiTileIdWidth ),
          .UserWidth   (1              ),
          .axi_req_t   (axi_tile_req_t ),
          .axi_resp_t  (axi_tile_resp_t)
        ) i_axi_burst_splitter (
          .clk_i     (clk_i                  ),
          .rst_ni    (rst_ni                 ),
          .slv_req_i (axi_l2_req[i]          ),
          .slv_resp_o(axi_l2_resp[i]         ),
          .mst_req_o (axi_l2_req_splitted[i] ),
          .mst_resp_i(axi_l2_resp_splitted[i])
        );
      end: brust_splitter
    end else begin : splitter_bypass
      // Do not need a splitter
      assign axi_l2_req_splitted  = axi_l2_req;
      assign axi_l2_resp          = axi_l2_resp_splitted;
    end: splitter_bypass
  endgenerate

  localparam int unsigned ConstantBits = $clog2(L2BankBeWidth * Interleave);
  localparam int unsigned ScrambleBits = (NumDrams == 1) ? 1 : $clog2(NumDrams);
  localparam int unsigned ReminderBits = AddrWidth - ScrambleBits - ConstantBits;
  // req.aw scrambling
  logic [NumAXIMasters-1:0][ConstantBits-1:0] aw_const;
  logic [NumAXIMasters-1:0][ScrambleBits-1:0] aw_scramble;
  logic [NumAXIMasters-1:0][ReminderBits-1:0] aw_reminder;
  logic [NumAXIMasters-1:0][AddrWidth-1   :0] aw_scramble_addr;
  // req.ar scrambling
  logic [NumAXIMasters-1:0][ConstantBits-1:0] ar_const;
  logic [NumAXIMasters-1:0][ScrambleBits-1:0] ar_scramble;
  logic [NumAXIMasters-1:0][ReminderBits-1:0] ar_reminder;
  logic [NumAXIMasters-1:0][AddrWidth-1   :0] ar_scramble_addr;

  for (genvar i = 0; unsigned'(i) < NumAXIMasters; i++) begin: gen_dram_scrambler
    assign aw_const[i]         = axi_l2_req_splitted[i].aw.addr[ConstantBits-1 : 0];
    assign aw_scramble[i]      = axi_l2_req_splitted[i].aw.addr[ScrambleBits+ConstantBits-1 : ConstantBits];
    assign aw_reminder[i]      = axi_l2_req_splitted[i].aw.addr[AddrWidth-1 : ScrambleBits+ConstantBits];
    assign aw_scramble_addr[i] = {aw_scramble[i], aw_reminder[i], aw_const[i]};

    assign ar_const[i]         = axi_l2_req_splitted[i].ar.addr[ConstantBits-1 : 0];
    assign ar_scramble[i]      = axi_l2_req_splitted[i].ar.addr[ScrambleBits+ConstantBits-1 : ConstantBits];
    assign ar_reminder[i]      = axi_l2_req_splitted[i].ar.addr[AddrWidth-1 : ScrambleBits+ConstantBits];
    assign ar_scramble_addr[i] = {ar_scramble[i], ar_reminder[i], ar_const[i]};

    // Scrambled AXI req assignment
    always_comb begin
      axi_l2_req_interleaved[i]         = axi_l2_req_splitted[i];
      axi_l2_req_interleaved[i].aw.addr = aw_scramble_addr[i];
      axi_l2_req_interleaved[i].ar.addr = ar_scramble_addr[i];
    end
  end: gen_dram_scrambler

  // DRAM Xbar rules
  for (genvar i = 0; unsigned'(i) < NumDramRules; i++) begin: gen_dram_xbar_rules
    logic [AddrWidth-1:0] start_dram_addr;
    logic [AddrWidth-1:0] end_dram_addr;
    assign start_dram_addr    = {{ScrambleBits{i}}, 1'b1, {AddrWidth-ScrambleBits-1{1'b0}}};
    assign end_dram_addr      = {{ScrambleBits{i}}, 1'b1, {AddrWidth-ScrambleBits-1{1'b1}}};
    assign dram_xbar_rules[i] = '{idx: i, start_addr: start_dram_addr, end_addr: end_dram_addr};
  end: gen_dram_xbar_rules

  // AXI Crossbar
  localparam xbar_cfg_t DRAMXBarCfg = '{
    NoSlvPorts         : NumAXIMasters,
    NoMstPorts         : NumDrams,
    MaxMstTrans        : 8,
    MaxSlvTrans        : 4,
    FallThrough        : 1'b0,
    LatencyMode        : axi_pkg::CUT_MST_PORTS,
    PipelineStages     : 0,
    AxiIdWidthSlvPorts : AxiTileIdWidth,
    AxiIdUsedSlvPorts  : AxiTileIdWidth,
    UniqueIds          : 0,
    AxiAddrWidth       : AddrWidth,
    AxiDataWidth       : AxiDataWidth,
    NoAddrRules        : NumDramRules
  };

  axi_xbar #(
    .Cfg          (DRAMXBarCfg      ),
    .slv_aw_chan_t(axi_tile_aw_t    ),
    .mst_aw_chan_t(axi_system_aw_t  ),
    .w_chan_t     (axi_system_w_t   ),
    .slv_b_chan_t (axi_tile_b_t     ),
    .mst_b_chan_t (axi_system_b_t   ),
    .slv_ar_chan_t(axi_tile_ar_t    ),
    .mst_ar_chan_t(axi_system_ar_t  ),
    .slv_r_chan_t (axi_tile_r_t     ),
    .mst_r_chan_t (axi_system_r_t   ),
    .slv_req_t    (axi_tile_req_t   ),
    .slv_resp_t   (axi_tile_resp_t  ),
    .mst_req_t    (axi_system_req_t ),
    .mst_resp_t   (axi_system_resp_t),
    .rule_t       (xbar_rule_32_t   )
  ) i_dram_xbar (
    .clk_i                (clk_i                 ),
    .rst_ni               (rst_ni                ),
    .test_i               (1'b0                  ),
    .slv_ports_req_i      (axi_l2_req_interleaved),
    .slv_ports_resp_o     (axi_l2_resp_splitted  ),
    .mst_ports_req_o      (dram_req_interleaved  ),
    .mst_ports_resp_i     (dram_resp             ),
    .addr_map_i           (dram_xbar_rules       ),
    .en_default_mst_port_i({NumAXIMasters{1'b1}} ),
    .default_mst_port_i   ('0                    )
  );

  // Scrambled Addr reset, and detect base address before go to DRAM
  for (genvar i = 0; unsigned'(i) < NumDrams; i++) begin: gen_dram_scrambler_reset
    // req.aw scrambling
    logic [ConstantBits-1:0] aw_const;
    logic [ScrambleBits-1:0] aw_scramble;
    logic [ReminderBits-1:0] aw_reminder;
    logic [AddrWidth-1   :0] aw_scramble_addr_reset;
    assign aw_scramble = dram_req_interleaved[i].aw.addr[AddrWidth-1 : AddrWidth-ScrambleBits];
    assign aw_reminder = dram_req_interleaved[i].aw.addr[AddrWidth-ScrambleBits-1 : ConstantBits] - L2MemoryBaseAddr[AddrWidth-1: AddrWidth-ReminderBits];
    assign aw_const    = dram_req_interleaved[i].aw.addr[ConstantBits-1 : 0];

    if (NumDrams == 1) begin
      assign aw_scramble_addr_reset = {aw_reminder, aw_scramble, aw_const};
    end else begin
      assign aw_scramble_addr_reset = {{ScrambleBits{1'b0}}, aw_reminder, aw_const};
    end

    // req.ar scrambling
    logic [ConstantBits-1:0] ar_const;
    logic [ScrambleBits-1:0] ar_scramble;
    logic [ReminderBits-1:0] ar_reminder;
    logic [AddrWidth-1   :0] ar_scramble_addr_reset;
    assign ar_scramble = dram_req_interleaved[i].ar.addr[AddrWidth-1 : AddrWidth-ScrambleBits];
    assign ar_reminder = dram_req_interleaved[i].ar.addr[AddrWidth-ScrambleBits-1 : ConstantBits] - L2MemoryBaseAddr[AddrWidth-1: AddrWidth-ReminderBits];
    assign ar_const    = dram_req_interleaved[i].ar.addr[ConstantBits-1 : 0];

    if (NumDrams == 1) begin
      assign ar_scramble_addr_reset = {ar_reminder, ar_scramble, ar_const};
    end else begin
      assign ar_scramble_addr_reset = {{ScrambleBits{1'b0}}, ar_reminder, ar_const};
    end

    // Scrambled AXI req assignment
    always_comb begin
      dram_req[i]         = dram_req_interleaved[i];
      dram_req[i].aw.addr = aw_scramble_addr_reset;
      dram_req[i].ar.addr = ar_scramble_addr_reset;
    end
  end: gen_dram_scrambler_reset

  for (genvar i = 0; unsigned'(i) < NumDrams; i++) begin: gen_drams
    axi_dram_sim #(
        .AxiAddrWidth(AddrWidth        ),
        .AxiDataWidth(AxiDataWidth     ),
        .AxiIdWidth  (AxiSystemIdWidth ),
        .AxiUserWidth(1                ),
        .DRAMType    ("HBM2"           ),
        .BASE        ('b0              ),
        .axi_req_t   (axi_system_req_t ),
        .axi_resp_t  (axi_system_resp_t),
        .axi_ar_t    (axi_system_ar_t  ),
        .axi_r_t     (axi_system_r_t   ),
        .axi_aw_t    (axi_system_aw_t  ),
        .axi_w_t     (axi_system_w_t   ),
        .axi_b_t     (axi_system_b_t   )
    ) i_axi_dram_sim (
        .clk_i,
        .rst_ni,
        .axi_req_i (dram_req[i] ),
        .axi_resp_o(dram_resp[i])
    );
  end: gen_drams
`endif

  /*************
   *  Bootrom  *
   *************/

  // Memory
  logic      bootrom_req;
  logic      bootrom_rvalid;
  addr_t     bootrom_addr;
  axi_data_t bootrom_rdata;

  axi2mem #(
    .axi_req_t  (axi_system_req_t ),
    .axi_resp_t (axi_system_resp_t),
    .AddrWidth  (AddrWidth        ),
    .DataWidth  (AxiDataWidth     ),
    .IdWidth    (AxiSystemIdWidth ),
    .NumBanks   (1                ),
    .BufDepth   (2                )
  ) i_axi2mem_bootrom (
    .clk_i        (clk_i                   ),
    .rst_ni       (rst_ni                  ),

    .busy_o       (/*unsused*/             ),

    .axi_req_i    (axi_periph_req[Bootrom] ),
    .axi_resp_o   (axi_periph_resp[Bootrom]),

    .mem_req_o    (bootrom_req             ),
    .mem_gnt_i    (bootrom_req             ),
    .mem_addr_o   (bootrom_addr            ),
    .mem_wdata_o  (/*unused*/              ),
    .mem_strb_o   (/*unused*/              ),
    .mem_atop_o   (/*unused*/              ),
    .mem_we_o     (/*unused*/              ),
    .mem_rvalid_i (bootrom_rvalid          ),
    .mem_rdata_i  (bootrom_rdata           )
  );

  `FF(bootrom_rvalid, bootrom_req, 1'b0, clk_i, rst_ni)

  bootrom i_bootrom (
    .clk_i  (clk_i        ),
    .req_i  (bootrom_req  ),
    .addr_i (bootrom_addr ),
    .rdata_o(bootrom_rdata)
  );

  /***********************
   *  Control Registers  *
   ***********************/

  localparam NumPeriphs = 2; // Control registers + DMA

  typedef enum logic [$clog2(NumPeriphs) - 1:0] {
    CtrlRegisters,
    DMA
  } axi_lite_xbar_slave_target;

  axi_periph_req_t                     axi_periph_narrow_req;
  axi_periph_resp_t                    axi_periph_narrow_resp;
  axi_lite_slv_req_t                   axi_lite_mst_req;
  axi_lite_slv_resp_t                  axi_lite_mst_resp;
  axi_lite_slv_req_t  [NumPeriphs-1:0] axi_lite_slv_req;
  axi_lite_slv_resp_t [NumPeriphs-1:0] axi_lite_slv_resp;

  localparam xbar_cfg_t AXILiteXBarCfg = '{
    NoSlvPorts         : 1,
    NoMstPorts         : NumPeriphs,
    MaxMstTrans        : 1,
    MaxSlvTrans        : 1,
    FallThrough        : 1'b0,
    LatencyMode        : axi_pkg::NO_LATENCY,
    PipelineStages     : 0,
    AxiIdWidthSlvPorts : 0, /* Not used for AXI lite */
    AxiIdUsedSlvPorts  : 0, /* Not used for AXI lite */
    UniqueIds          : 0, /* Not used for AXI lite */
    AxiAddrWidth       : AddrWidth,
    AxiDataWidth       : AxiLiteDataWidth,
    NoAddrRules        : NumPeriphs
  };

  localparam addr_t CtrlRegistersBaseAddr = 32'h4000_0000;
  localparam addr_t CtrlRegistersEndAddr  = 32'h4001_0000;
  localparam addr_t DMABaseAddr           = 32'h4001_0000;
  localparam addr_t DMAEndAddr            = 32'h4002_0000;

  xbar_rule_32_t [NumPeriphs-1:0] axi_lite_xbar_rules;
  assign axi_lite_xbar_rules = '{
    '{idx: CtrlRegisters, start_addr: CtrlRegistersBaseAddr, end_addr: CtrlRegistersEndAddr},
    '{idx: DMA, start_addr: DMABaseAddr, end_addr: DMAEndAddr}
  };

  axi_dw_converter #(
    .AxiMaxReads         (1                ), // Number of outstanding reads
    .AxiSlvPortDataWidth (AxiDataWidth     ), // Data width of the slv port
    .AxiMstPortDataWidth (AxiLiteDataWidth ), // Data width of the mst port
    .AxiAddrWidth        (AddrWidth        ), // Address width
    .AxiIdWidth          (AxiSystemIdWidth ), // ID width
    .aw_chan_t           (axi_system_aw_t  ), // AW Channel Type
    .mst_w_chan_t        (axi_periph_w_t   ), //  W Channel Type for the mst port
    .slv_w_chan_t        (axi_system_w_t   ), //  W Channel Type for the slv port
    .b_chan_t            (axi_system_b_t   ), //  B Channel Type
    .ar_chan_t           (axi_system_ar_t  ), // AR Channel Type
    .mst_r_chan_t        (axi_periph_r_t   ), //  R Channel Type for the mst port
    .slv_r_chan_t        (axi_system_r_t   ), //  R Channel Type for the slv port
    .axi_mst_req_t       (axi_periph_req_t ), // AXI Request Type for mst ports
    .axi_mst_resp_t      (axi_periph_resp_t), // AXI Response Type for mst ports
    .axi_slv_req_t       (axi_system_req_t ), // AXI Request Type for slv ports
    .axi_slv_resp_t      (axi_system_resp_t)  // AXI Response Type for slv ports
  ) i_axi_dw_converter_ctrl (
    .clk_i      (clk_i                       ),
    .rst_ni     (rst_ni                      ),
    // Slave interface
    .slv_req_i  (axi_periph_req[Peripherals] ),
    .slv_resp_o (axi_periph_resp[Peripherals]),
    // Master interface
    .mst_req_o  (axi_periph_narrow_req       ),
    .mst_resp_i (axi_periph_narrow_resp      )
  );

  axi_to_axi_lite #(
    .AxiAddrWidth   (AddrWidth          ),
    .AxiDataWidth   (AxiLiteDataWidth   ),
    .AxiIdWidth     (AxiSystemIdWidth   ),
    .AxiUserWidth   (1                  ),
    .AxiMaxReadTxns (1                  ),
    .AxiMaxWriteTxns(1                  ),
    .FallThrough    (1'b0               ),
    .full_req_t     (axi_periph_req_t   ),
    .full_resp_t    (axi_periph_resp_t  ),
    .lite_req_t     (axi_lite_slv_req_t ),
    .lite_resp_t    (axi_lite_slv_resp_t)
  ) i_axi_to_axi_lite (
    .clk_i     (clk_i                 ),
    .rst_ni    (rst_ni                ),
    .test_i    (1'b0                  ),
    .slv_req_i (axi_periph_narrow_req ),
    .slv_resp_o(axi_periph_narrow_resp),
    .mst_req_o (axi_lite_mst_req      ),
    .mst_resp_i(axi_lite_mst_resp     )
  );

  axi_lite_xbar #(
    .Cfg       (AXILiteXBarCfg     ),
    .aw_chan_t (axi_lite_slv_aw_t  ),
    .w_chan_t  (axi_lite_slv_w_t   ),
    .b_chan_t  (axi_lite_slv_b_t   ),
    .ar_chan_t (axi_lite_slv_ar_t  ),
    .r_chan_t  (axi_lite_slv_r_t   ),
    .axi_req_t (axi_lite_slv_req_t ),
    .axi_resp_t(axi_lite_slv_resp_t),
    .rule_t    (xbar_rule_32_t     )
  ) i_axi_lite_xbar (
    .clk_i                (clk_i              ),
    .rst_ni               (rst_ni             ),
    .test_i               (1'b0               ),
    .slv_ports_req_i      (axi_lite_mst_req   ),
    .slv_ports_resp_o     (axi_lite_mst_resp  ),
    .mst_ports_req_o      (axi_lite_slv_req   ),
    .mst_ports_resp_i     (axi_lite_slv_resp  ),
    .addr_map_i           (axi_lite_xbar_rules),
    .en_default_mst_port_i('1                 ),
    .default_mst_port_i   (CtrlRegisters      )
  );

  ctrl_registers #(
    .TCDMBaseAddr     (TCDMBaseAddr       ),
    .TCDMSize         (TCDMSize           ),
    .NumCores         (NumCores           ),
    .axi_lite_req_t (axi_lite_slv_req_t ),
    .axi_lite_resp_t(axi_lite_slv_resp_t)
  ) i_ctrl_registers (
    .clk_i                (clk_i                           ),
    .rst_ni               (rst_ni                          ),
    .axi_lite_slave_req_i (axi_lite_slv_req[CtrlRegisters] ),
    .axi_lite_slave_resp_o(axi_lite_slv_resp[CtrlRegisters]),
    .eoc_o                (/* Unused */                    ),
    .eoc_valid_o          (eoc_valid_o                     ),
    .wake_up_o            (wake_up                         ),
    .ro_cache_ctrl_o      (ro_cache_ctrl                   )
  );

  mempool_dma #(
    .axi_lite_req_t(axi_lite_slv_req_t       ),
    .axi_lite_rsp_t(axi_lite_slv_resp_t      ),
    .burst_req_t   (dma_req_t                ),
    .NumBackends   (NumGroups                ),
    .DmaIdWidth    (1                        )
  ) i_mempool_dma (
    .clk_i           (clk_i                  ),
    .rst_ni          (rst_ni                 ),
    .config_req_i    (axi_lite_slv_req[DMA]  ),
    .config_res_o    (axi_lite_slv_resp[DMA] ),
    .burst_req_o     (dma_req                ),
    .valid_o         (dma_req_valid          ),
    .ready_i         (dma_req_ready          ),
    .backend_idle_i  (dma_meta.backend_idle  ),
    .trans_complete_i(dma_meta.trans_complete),
    .dma_id_o        (dma_id                 )
  );

  assign busy_o = 1'b0;

  // From MemPool to the Host
  assign mst_req_o                 = axi_periph_req[External];
  assign axi_periph_resp[External] = mst_resp_i;
  // From the Host to MemPool
  axi_id_remap #(
    .AxiSlvPortIdWidth   (AxiSystemIdWidth ),
    .AxiSlvPortMaxUniqIds(1                ),
    .AxiMaxTxnsPerId     (1                ),
    .AxiMstPortIdWidth   (AxiTileIdWidth   ),
    .slv_req_t           (axi_system_req_t ),
    .slv_resp_t          (axi_system_resp_t),
    .mst_req_t           (axi_tile_req_t   ),
    .mst_resp_t          (axi_tile_resp_t  )
  ) i_axi_id_remap (
    .clk_i     (clk_i                        ),
    .rst_ni    (rst_ni                       ),
    .slv_req_i (slv_req_i                    ),
    .slv_resp_o(slv_resp_o                   ),
    .mst_req_o (axi_mst_req[NumAXIMasters-1] ),
    .mst_resp_i(axi_mst_resp[NumAXIMasters-1])
  );

endmodule : mempool_system
