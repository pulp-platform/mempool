// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"
`include "register_interface/typedef.svh"

module ctrl_registers
  import mempool_pkg::ro_cache_ctrl_t;
#(
  parameter int DataWidth                      = 32,
  // Parameters
  parameter logic [DataWidth-1:0] TCDMBaseAddr = 0,
  parameter logic [DataWidth-1:0] TCDMSize     = 0,
  parameter logic [DataWidth-1:0] NumCores     = 0,
  // AXI Structs
  parameter type axi_lite_req_t                = logic,
  parameter type axi_lite_resp_t               = logic
) (
  input  logic                           clk_i,
  input  logic                           rst_ni,
  // AXI Bus
  input  axi_lite_req_t                  axi_lite_slave_req_i,
  output axi_lite_resp_t                 axi_lite_slave_resp_o,
  // Control registers
  output logic      [DataWidth-1:0]      eoc_o,
  output logic                           eoc_valid_o,
  output logic      [NumCores-1:0]       wake_up_o,
  output ro_cache_ctrl_t                 ro_cache_ctrl_o
);

  import mempool_pkg::AddrWidth;
  import control_registers_reg_pkg::*;

  /***************
   *  Registers  *
   ***************/
  `REG_BUS_TYPEDEF_ALL(ctrl_reg, logic[AddrWidth-1:0], logic[DataWidth-1:0], logic[DataWidth/8-1:0]);
  ctrl_reg_req_t ctrl_reg_req;
  ctrl_reg_rsp_t ctrl_reg_rsp;
  control_registers_reg2hw_t ctrl_reg2hw;
  control_registers_hw2reg_t ctrl_hw2reg;

  axi_lite_to_reg #(
    .ADDR_WIDTH    (AddrWidth      ),
    .DATA_WIDTH    (DataWidth      ),
    .BUFFER_DEPTH  (1              ),
    .DECOUPLE_W    (0              ),
    .axi_lite_req_t(axi_lite_req_t ),
    .axi_lite_rsp_t(axi_lite_resp_t),
    .reg_req_t     (ctrl_reg_req_t ),
    .reg_rsp_t     (ctrl_reg_rsp_t )
  ) i_axi_lite_to_reg (
    .clk_i         (clk_i                ),
    .rst_ni        (rst_ni               ),
    .axi_lite_req_i(axi_lite_slave_req_i ),
    .axi_lite_rsp_o(axi_lite_slave_resp_o),
    .reg_req_o     (ctrl_reg_req         ),
    .reg_rsp_i     (ctrl_reg_rsp         )
  );

  control_registers_reg_top #(
    .reg_req_t(ctrl_reg_req_t),
    .reg_rsp_t(ctrl_reg_rsp_t)
  ) i_control_registers_reg_top (
    .clk_i    (clk_i       ),
    .rst_ni   (rst_ni      ),
    .reg_req_i(ctrl_reg_req),
    .reg_rsp_o(ctrl_reg_rsp),
    .reg2hw   (ctrl_reg2hw ),
    .hw2reg   (ctrl_hw2reg ),
    .devmode_i(1'b0        )
  );

  /************************
   *  External Registers  *
   ************************/
  // These registers have hardcoded values (read-only)
  assign ctrl_hw2reg.nr_cores_reg.d = NumCores;
  assign ctrl_hw2reg.tcdm_start_address.d = TCDMBaseAddr;
  assign ctrl_hw2reg.tcdm_end_address.d = TCDMBaseAddr + TCDMSize;

  // These registers are external because they have special reset values. But they are read and
  // write so we need to instantiate an actual register
  typedef struct packed {
    logic [AddrWidth-1:0] start_addr;
    logic [AddrWidth-1:0] end_addr;
  } ro_cache_region_t;
  ro_cache_region_t [ROCacheNumAddrRules-1:0] ro_cache_regions;
  assign ro_cache_regions = '{
    '{start_addr: 32'h0000_000C, end_addr: 32'h0000_0010},
    '{start_addr: 32'h0000_0008, end_addr: 32'h0000_000C},
    '{start_addr: 32'hA000_0000, end_addr: 32'hA000_1000},
    '{start_addr: 32'h8000_0000, end_addr: 32'h8000_1000}
  };
  for (genvar i = 0; i < ROCacheNumAddrRules; i++) begin : gen_ro_cache_reg
    `FFL(ctrl_hw2reg.ro_cache_start[i].d, ctrl_reg2hw.ro_cache_start[i].q, ctrl_reg2hw.ro_cache_start[i].qe, ro_cache_regions[i].start_addr)
    `FFL(ctrl_hw2reg.ro_cache_end[i].d, ctrl_reg2hw.ro_cache_end[i].q, ctrl_reg2hw.ro_cache_end[i].qe, ro_cache_regions[i].end_addr)
  end

  /************************
   *  Wakeup Pulse Logic  *
   ************************/
  import mempool_pkg::NumCoresPerCluster;
  import mempool_pkg::NumCoresPerGroup;
  import mempool_pkg::NumCoresPerTile;
  import mempool_pkg::NumTilesPerGroup;
  import mempool_pkg::NumClusters;
  import mempool_pkg::NumGroups;

  // Delay the write-enable signal by one cycle so it arrives
  // simultaneously with the registered values
  logic wake_up_pulse;
  logic [MAX_NumGroups-1:0] wake_up_tile_pulse;
  logic wake_up_group_pulse;
  logic wake_up_cluster_pulse;

  `FF(wake_up_pulse, ctrl_reg2hw.wake_up.qe, '0)
  for (genvar i = 0; i < MAX_NumGroups; i++) begin : gen_wake_up_tile_reg
    `FF(wake_up_tile_pulse[i], ctrl_reg2hw.wake_up_tile[i].qe, '0)
  end
  `FF(wake_up_group_pulse, ctrl_reg2hw.wake_up_group.qe, '0)
  `FF(wake_up_cluster_pulse, ctrl_reg2hw.wake_up_cluster.qe, '0)

  always_comb begin
    wake_up_o = '0;
    // converts 32-bit core wake-up into a 'NumCores'-bit mask
    if (wake_up_pulse) begin
      if (ctrl_reg2hw.wake_up.q < NumCores) begin
        wake_up_o = 1 << ctrl_reg2hw.wake_up.q;
      end else begin
        wake_up_o = {NumCores{1'b1}};
      end
    end
    // converts 32-bit tile wake-up mask into a 'NumCores'-bit mask
    for(int g = 0; g < NumGroups; g = g + 1) begin
      if (wake_up_tile_pulse[g]) begin
        if (ctrl_reg2hw.wake_up_tile[g].q <= {NumTilesPerGroup{1'b1}}) begin
          for (int t = 0; t < NumTilesPerGroup; t = t + 1) begin
            wake_up_o[NumCoresPerGroup * g + NumCoresPerTile * t +: NumCoresPerTile] = {NumCoresPerTile{ctrl_reg2hw.wake_up_tile[g].q[t]}};
          end
        end
      end
    end
    // converts 32-bit group wake-up mask into a 'NumCores'-bit mask
    if (wake_up_group_pulse) begin
      if (ctrl_reg2hw.wake_up_group.q <= {NumGroups{1'b1}}) begin
        for(int i = 0; i < NumGroups; i = i + 1) begin
          wake_up_o[NumCoresPerGroup * i +: NumCoresPerGroup] = {NumCoresPerGroup{ctrl_reg2hw.wake_up_group.q[i]}};
        end
      end else if (ctrl_reg2hw.wake_up_group.q == {DataWidth{1'b1}}) begin
        wake_up_o = {NumCores{1'b1}};
      end
    end
    // converts 32-bit cluster wake-up mask into a 'NumCores'-bit mask
    if (wake_up_cluster_pulse) begin
      if (ctrl_reg2hw.wake_up_cluster.q <= {NumClusters{1'b1}}) begin
        for(int i = 0; i < NumClusters; i = i + 1) begin
          wake_up_o[NumCoresPerCluster * i +: NumCoresPerCluster] = {NumCoresPerCluster{ctrl_reg2hw.wake_up_cluster.q[i]}};
        end
      end else if (ctrl_reg2hw.wake_up_cluster.q == {DataWidth{1'b1}}) begin
        wake_up_o = {NumCores{1'b1}};
      end
    end
  end

  /***********************
   *  Output Assignment  *
   ***********************/
  assign eoc_o       = ctrl_reg2hw.eoc.q >> 1;
  assign eoc_valid_o = ctrl_reg2hw.eoc.q[0];

  assign ro_cache_ctrl_o.enable        = ctrl_reg2hw.ro_cache_enable.q[0];
  assign ro_cache_ctrl_o.flush_valid   = ctrl_reg2hw.ro_cache_flush.q[0];
  for (genvar i = 0; i < ROCacheNumAddrRules; i++) begin : gen_ro_cache_out
    assign ro_cache_ctrl_o.start_addr[i] = ctrl_hw2reg.ro_cache_start[i].d;
    assign ro_cache_ctrl_o.end_addr[i] = ctrl_hw2reg.ro_cache_end[i].d;
  end

  /******************
   *   Assertions   *
   ******************/
  if (NumGroups > MAX_NumGroups)
    $error("[ctrl_registers] Number of groups exceeds the maximum supported.");

  if (MAX_NumGroups != mempool_pkg::MAX_NumGroups)
    $error("[ctrl_registers] MAX_NumGroups parameter does not match the one from mempool_pkg.");

  if (ROCacheNumAddrRules != mempool_pkg::ROCacheNumAddrRules)
    $error("[ctrl_registers] ROCacheNumAddrRules parameter does not match the one from mempool_pkg.");

endmodule : ctrl_registers
