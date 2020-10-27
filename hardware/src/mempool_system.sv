import mempool_pkg::*;
import axi_pkg::xbar_cfg_t;
import axi_pkg::xbar_rule_32_t;

`include "axi/assign.svh"

module mempool_system
#(
    // Mempool
    parameter int unsigned NumCores = 1,
    parameter int unsigned BankingFactor = 4,
    // TCDM
    parameter addr_t TCDMBaseAddr = 32'b0,
    // Boot address
    parameter addr_t BootAddr = 32'h0000_0000,
    // Dependant parameters. DO NOT CHANGE!
    parameter int unsigned NumTiles = NumCores / NumCoresPerTile
    //parameter int unsigned NumAXIMasters = NumTiles + 1
  ) (
    input logic                    clk_i,
    input logic                    rst_ni,

    input  logic  fetch_en_i,
    output logic  eoc_valid_o,
    output logic  busy_o,

    output axi_system_req_t              ext_req_o,
    input  axi_system_resp_t             ext_resp_i,

    input  axi_tile_req_t                  ext_req_i,
    output axi_tile_resp_t                 ext_resp_o,

    input  axi_lite_slv_req_t         rab_conf_req_i,
    output axi_lite_slv_resp_t        rab_conf_resp_o
  );

  localparam NumTilesPerGroup = NumTiles / NumGroups;
  localparam NumBanks = NumCores * BankingFactor;
  localparam TCDMSize = NumBanks * TCDMSizePerBank;
  localparam L2AddrWidth = 18;

  /*********
   *  AXI  *
   *********/

  localparam NumAXIMasters = NumTiles + 1;
  localparam NumAXISlaves  = 3;
  localparam NumRules  = NumAXISlaves-1;

  typedef enum logic [$clog2(NumAXISlaves)-1:0] {
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
    NoSlvPorts        : NumAXIMasters,
    NoMstPorts        : NumAXISlaves,
    MaxMstTrans       : 4,
    MaxSlvTrans       : 4,
    FallThrough       : 1'b0,
    LatencyMode       : axi_pkg::CUT_MST_PORTS,
    AxiIdWidthSlvPorts: AxiTileIdWidth,
    AxiIdUsedSlvPorts : AxiTileIdWidth,
    AxiAddrWidth      : AddrWidth,
    AxiDataWidth      : DataWidth,
    NoAddrRules       : NumRules
  };

  /*************
   *  MEMPOOL  *
   ************/

  mempool #(
    .NumCores     (NumCores                        ),
    .BankingFactor(BankingFactor                   ),
    .TCDMBaseAddr (TCDMBaseAddr                    ),
    .BootAddr     (BootAddr                        ),
    .NumAXIMasters(NumAXIMasters-1                 )
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
  localparam addr_t CtrlRegistersEndAddr = 32'h4000_FFFF;
  localparam addr_t L2MemoryBaseAddr = 32'h8000_0000;
  localparam addr_t L2MemoryEndAddr = 32'hBFFF_FFFF;

  xbar_rule_32_t [NumRules-1:0] xbar_routing_rules = '{
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
    .AXI_DATA_WIDTH (DataWidth       ),
    .AXI_ID_WIDTH   (AxiSystemIdWidth),
    .AXI_USER_WIDTH (1               )
  ) axi_l2memory_slave ();

  // Assign slave
  `AXI_ASSIGN_FROM_REQ(axi_l2memory_slave, axi_mem_req[L2Memory] );
  `AXI_ASSIGN_TO_RESP (axi_mem_resp[L2Memory], axi_l2memory_slave);

  // Memory
  logic  mem_req;
  addr_t mem_addr;
  data_t mem_wdata;
  strb_t mem_strb;
  logic  mem_we;
  data_t mem_rdata;

  axi2mem #(
    .AXI_ADDR_WIDTH(AddrWidth       ),
    .AXI_DATA_WIDTH(DataWidth       ),
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
    .DataWidth(DataWidth     ),
    .NumWords (2**L2AddrWidth),
    .NumPorts (1             )
  ) l2_mem (
    .clk_i  (clk_i                              ),
    .rst_ni (rst_ni                             ),
    .req_i  (mem_req                            ),
    .we_i   (mem_we                             ),
    .addr_i (mem_addr[ByteOffset +: L2AddrWidth]),
    .wdata_i(mem_wdata                          ),
    .be_i   (mem_strb                           ),
    .rdata_o(mem_rdata                          )
  );

 /***********************
   *  Control Registers  *
   ***********************/

  axi_lite_slv_req_t  axi_lite_ctrl_registers_req;
  axi_lite_slv_resp_t axi_lite_ctrl_registers_resp;

  axi_to_axi_lite #(
    .AxiAddrWidth   (AddrWidth          ),
    .AxiDataWidth   (DataWidth          ),
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

  /***********************
   * Host/External Ports *
   ***********************/

  // Assign Host Master
  assign axi_mst_req[NumAXIMasters-1] = ext_req_i;
  assign ext_resp_o = axi_mst_resp[NumAXIMasters-1];

  // Assign Host Slave
  assign ext_req_o = axi_mem_req[External];
  assign axi_mem_resp[External] = ext_resp_i;

endmodule : mempool_system
