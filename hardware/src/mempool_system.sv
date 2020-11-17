import mempool_pkg::*;
import axi_pkg::xbar_cfg_t;
import axi_pkg::xbar_rule_32_t;

`include "axi/assign.svh"

module mempool_system #(
    // Mempool
    parameter int unsigned NumCores      = 1,
    parameter int unsigned BankingFactor = 4,
    // TCDM
    parameter addr_t TCDMBaseAddr = 32'b0,
    // Boot address
    parameter addr_t BootAddr = 32'h0000_0000
  ) (
    input logic                clk_i,
    input logic                rst_ni,

    input  logic               fetch_en_i,
    output logic               eoc_valid_o,
    output logic               busy_o,

    output axi_system_req_t    ext_req_o,
    input  axi_system_resp_t   ext_resp_i,

    input  axi_system_req_t    ext_req_i,
    output axi_system_resp_t   ext_resp_o,

    input  axi_lite_slv_req_t  rab_conf_req_i,
    output axi_lite_slv_resp_t rab_conf_resp_o
  );

  localparam NumTiles         = NumCores / NumCoresPerTile;
  localparam NumTilesPerGroup = NumTiles / NumGroups;
  localparam NumBanks         = NumCores * BankingFactor;
  localparam TCDMSize         = NumBanks * TCDMSizePerBank;
  localparam L2AddrWidth      = 18;

  /*********
   *  AXI  *
   *********/

  localparam NumAXIMasters = NumTiles + 1; // +1 because the external host is also a master
  localparam NumAXISlaves  = 3;            // control regs, l2 memory and the external mst ports
  localparam NumRules      = NumAXISlaves - 1;

  typedef enum logic [$clog2(NumAXISlaves) - 1:0] {
    CtrlRegisters,
    L2Memory,
    External
  } axi_slave_target;

  axi_tile_req_t    [NumAXIMasters - 1:0] axi_mst_req;
  axi_tile_resp_t   [NumAXIMasters - 1:0] axi_mst_resp;
  axi_system_req_t  [NumAXISlaves - 1:0]  axi_mem_req;
  axi_system_resp_t [NumAXISlaves - 1:0]  axi_mem_resp;
  logic             [NumCores - 1:0]      wake_up;
  logic             [DataWidth - 1:0]     eoc;

  localparam xbar_cfg_t XBarCfg = '{
    NoSlvPorts         : NumAXIMasters,
    NoMstPorts         : NumAXISlaves,
    MaxMstTrans        : 4,
    MaxSlvTrans        : 4,
    FallThrough        : 1'b0,
    LatencyMode        : axi_pkg::CUT_MST_PORTS,
    AxiIdWidthSlvPorts : AxiTileIdWidth,
    AxiIdUsedSlvPorts  : AxiTileIdWidth,
    AxiAddrWidth       : AddrWidth,
    AxiDataWidth       : DataWidth,
    NoAddrRules        : NumRules
  };

  /*************
   *  MEMPOOL  *
   ************/

  mempool #(
    .NumCores     (NumCores       ),
    .BankingFactor(BankingFactor  ),
    .TCDMBaseAddr (TCDMBaseAddr   ),
    .BootAddr     (BootAddr       ),
    .NumAXIMasters(NumAXIMasters-1)
  ) i_mempool (
    .clk_i         (clk_i                          ),
    .rst_ni        (rst_ni                         ),
    .wake_up_i     (wake_up                        ),
    .testmode_i    (1'b0                           ),
    .scan_enable_i (1'b0                           ),
    .scan_data_i   (1'b0                           ),
    .scan_data_o   (/* Unused */                   ),
    .axi_mst_req_o (axi_mst_req[NumAXIMasters-2:0] ),
    .axi_mst_resp_i(axi_mst_resp[NumAXIMasters-2:0])
  );

  /**********************
   *  AXI Interconnect  *
   **********************/

  localparam addr_t CtrlRegistersBaseAddr = 32'h4000_0000;
  localparam addr_t CtrlRegistersEndAddr  = 32'h4000_FFFF;
  localparam addr_t L2MemoryBaseAddr      = 32'h8000_0000;
  localparam addr_t L2MemoryEndAddr       = 32'hBFFF_FFFF;

  xbar_rule_32_t [NumRules - 1:0] xbar_routing_rules = '{
    '{idx: CtrlRegisters, start_addr: CtrlRegistersBaseAddr, end_addr: CtrlRegistersEndAddr},
    '{idx: L2Memory, start_addr: L2MemoryBaseAddr, end_addr: L2MemoryEndAddr}
  };

  axi_xbar #(
    .Cfg          (XBarCfg          ),
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
  ) i_xbar (
    .clk_i                (clk_i                    ),
    .rst_ni               (rst_ni                   ),
    .test_i               (1'b0                     ),
    .slv_ports_req_i      (axi_mst_req              ),
    .slv_ports_resp_o     (axi_mst_resp             ),
    .mst_ports_req_o      (axi_mem_req              ),
    .mst_ports_resp_i     (axi_mem_resp             ),
    .addr_map_i           (xbar_routing_rules       ),
    .en_default_mst_port_i('1                       ), // default all slave ports to master port External
    .default_mst_port_i   ({NumAXIMasters{External}})
  );

  /********
   *  L2  *
   ********/

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AddrWidth       ),
    .AXI_DATA_WIDTH (AxiDataWidth    ),
    .AXI_ID_WIDTH   (AxiSystemIdWidth),
    .AXI_USER_WIDTH (1               )
  ) axi_l2memory_slave ();

  // Assign slave
  `AXI_ASSIGN_FROM_REQ(axi_l2memory_slave, axi_mem_req[L2Memory] );
  `AXI_ASSIGN_TO_RESP (axi_mem_resp[L2Memory], axi_l2memory_slave);

  // Memory
  logic  mem_req;
  addr_t mem_addr;
  axi_data_t mem_wdata;
  axi_strb_t mem_strb;
  logic  mem_we;
  axi_data_t mem_rdata;

  axi2mem #(
    .AXI_ADDR_WIDTH(AddrWidth       ),
    .AXI_DATA_WIDTH(AxiDataWidth    ),
    .AXI_ID_WIDTH  (AxiSystemIdWidth),
    .AXI_USER_WIDTH(1               )
  ) i_axi2mem (
    .clk_i (clk_i             ),
    .rst_ni(rst_ni            ),
    .slave (axi_l2memory_slave),
    .req_o (mem_req           ),
    .addr_o(mem_addr          ),
    .data_o(mem_wdata         ),
    .we_o  (mem_we            ),
    .be_o  (mem_strb          ),
    .data_i(mem_rdata         )
  );

  tc_sram #(
    .DataWidth(AxiDataWidth  ),
    .NumWords (2**L2AddrWidth),
    .NumPorts (1             )
  ) l2_mem (
    .clk_i  (clk_i                                ),
    .rst_ni (rst_ni                               ),
    .req_i  (mem_req                              ),
    .we_i   (mem_we                               ),
    .addr_i (mem_addr[L2ByteOffset +: L2AddrWidth]),
    .wdata_i(mem_wdata                            ),
    .be_i   (mem_strb                             ),
    .rdata_o(mem_rdata                            )
  );

  /***********************
   *  Control Registers  *
   ***********************/

  axi_lite_slv_req_t  axi_lite_ctrl_registers_req;
  axi_lite_slv_resp_t axi_lite_ctrl_registers_resp;

  axi_to_axi_lite #(
    .AxiAddrWidth   (AddrWidth          ),
    .AxiDataWidth   (AxiDataWidth       ),
    .AxiIdWidth     (AxiSystemIdWidth   ),
    .AxiUserWidth   (1                  ),
    .AxiMaxReadTxns (1                  ),
    .AxiMaxWriteTxns(1                  ),
    .FallThrough    (1'b0               ),
    .full_req_t     (axi_system_req_t   ),
    .full_resp_t    (axi_system_resp_t  ),
    .lite_req_t     (axi_lite_slv_req_t ),
    .lite_resp_t    (axi_lite_slv_resp_t)
  ) i_axi_to_axi_lite (
    .clk_i     (clk_i                       ),
    .rst_ni    (rst_ni                      ),
    .test_i    (1'b0                        ),
    .slv_req_i (axi_mem_req[CtrlRegisters]  ),
    .slv_resp_o(axi_mem_resp[CtrlRegisters] ),
    .mst_req_o (axi_lite_ctrl_registers_req ),
    .mst_resp_i(axi_lite_ctrl_registers_resp)
  );

  ctrl_registers #(
    .NumRegs        (5                  ),
    .TCDMBaseAddr   (TCDMBaseAddr       ),
    .TCDMSize       (TCDMSize           ),
    .NumCores       (NumCores           ),
    .axi_lite_req_t (axi_lite_slv_req_t ),
    .axi_lite_resp_t(axi_lite_slv_resp_t)
  ) i_ctrl_registers (
    .clk_i                (clk_i                       ),
    .rst_ni               (rst_ni                      ),
    .axi_lite_slave_req_i (axi_lite_ctrl_registers_req ),
    .axi_lite_slave_resp_o(axi_lite_ctrl_registers_resp),
    .tcdm_start_address_o (/* Unused */                ),
    .tcdm_end_address_o   (/* Unused */                ),
    .num_cores_o          (/* Unused */                ),
    .wake_up_o            (wake_up                     ),
    .eoc_o                (/* Unused */                ),
    .eoc_valid_o          (eoc_valid_o                 )
  );

  /***********
   * AXI RAB *
   ***********/

  axi_system_req_t  rab_slv_req;
  axi_system_resp_t rab_slv_resp;

  axi_rab_wrap #(
    .L1NumSlicesMemPool(4                  ),
    .L1NumSlicesHost   (4                  ),
    .L2Enable          (1'b0               ),
    .L2NumSets         (32                 ),
    .L2NumSetEntries   (32                 ),
    .L2NumParVaRams    (4                  ),
    .MhFifoDepth       (16                 ),
    .AxiAddrWidth      (AddrWidth          ),
    .AxiDataWidth      (AxiDataWidth       ),
    .AxiIdWidth        (AxiSystemIdWidth   ),
    .AxiUserWidth      (1                  ),
    .axi_req_t         (axi_system_req_t   ),
    .axi_resp_t        (axi_system_resp_t  ),
    .axi_lite_req_t    (axi_lite_slv_req_t ),
    .axi_lite_resp_t   (axi_lite_slv_resp_t)
  ) i_rab (
    .clk_i,
    .rst_ni,
    .from_mempool_req_i      (axi_mem_req[External] ),
    .from_mempool_resp_o     (axi_mem_resp[External]),
    .from_mempool_miss_irq_o (/*Unused*/            ),
    .from_mempool_multi_irq_o(/*Unused*/            ),
    .from_mempool_prot_irq_o (/*Unused*/            ),
    .to_host_req_o           (ext_req_o             ),
    .to_host_resp_i          (ext_resp_i            ),
    .from_host_req_i         (ext_req_i             ),
    .from_host_resp_o        (ext_resp_o            ),
    .from_host_miss_irq_o    (/*Unused*/            ),
    .from_host_multi_irq_o   (/*Unused*/            ),
    .from_host_prot_irq_o    (/*Unused*/            ),
    .to_mempool_req_o        (rab_slv_req           ),
    .to_mempool_resp_i       (rab_slv_resp          ),
    .mh_fifo_full_irq_o      (/*Unused*/            ),
    .conf_req_i              (rab_conf_req_i        ),
    .conf_resp_o             (rab_conf_resp_o       )
  );

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
    .slv_req_i (rab_slv_req                  ),
    .slv_resp_o(rab_slv_resp                 ),
    .mst_req_o (axi_mst_req[NumAXIMasters-1] ),
    .mst_resp_i(axi_mst_resp[NumAXIMasters-1])
  );

endmodule : mempool_system
