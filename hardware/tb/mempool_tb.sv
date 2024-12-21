// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

import "DPI-C" function void read_elf (input string filename);
import "DPI-C" function byte get_section (output longint address, output longint len);
import "DPI-C" context function byte read_section(input longint address, inout byte buffer[]);

`define wait_for(signal) \
  do \
    @(posedge clk); \
  while (!signal);

module mempool_tb;

  /*****************
   *  Definitions  *
   *****************/

  timeunit      1ns;
  timeprecision 1ps;

  import mempool_pkg::*;
  import floo_pkg::*;
  import axi_pkg::xbar_cfg_t;
  import axi_pkg::xbar_rule_32_t;
  import cf_math_pkg::idx_width;

  `ifdef BOOT_ADDR
  localparam BootAddr = `BOOT_ADDR;
  `else
  localparam BootAddr = 0;
  `endif

  localparam ClockPeriod = 2ns;
  localparam TA          = 0.2ns;
  localparam TT          = 0.8ns;

  localparam PollEoc     = 0;

 /********************************
   *  Clock and Reset Generation  *
   ********************************/

  logic clk;
  logic rst_n;

  // Toggling the clock
  always #(ClockPeriod/2) clk = !clk;

  // Controlling the reset
  initial begin
    clk   = 1'b1;
    rst_n = 1'b0;

    repeat (5)
      #(ClockPeriod);

    rst_n = 1'b1;
  end

  `ifdef DRAM
    dram_sim_engine #(.ClkPeriodNs(ClockPeriod)) i_dram_sim_engine (.clk_i(clk), .rst_ni(rst_n));
  `endif

  /*********
   *  AXI  *
   *********/

  `include "axi/assign.svh"

  localparam NumAXIMasters = 1;
  localparam NumAXISlaves  = 2;
  localparam NumRules  = NumAXISlaves-1;

  typedef enum logic [$clog2(NumAXISlaves)-1:0] {
    UART,
    Host
  } axi_slave_target;

  axi_system_req_t    [NumAXIMasters - 1:0] axi_mst_req;
  axi_system_resp_t   [NumAXIMasters - 1:0] axi_mst_resp;
  axi_tb_req_t        [NumAXISlaves - 1:0]  axi_mem_req;
  axi_tb_resp_t       [NumAXISlaves - 1:0]  axi_mem_resp;

  axi_system_req_t                          to_mempool_req;
  axi_system_resp_t                         to_mempool_resp;

  localparam xbar_cfg_t XBarCfg = '{
    NoSlvPorts        : NumAXIMasters,
    NoMstPorts        : NumAXISlaves,
    MaxMstTrans       : 4,
    MaxSlvTrans       : 4,
    FallThrough       : 1'b0,
    LatencyMode       : axi_pkg::CUT_MST_PORTS,
    PipelineStages    : 0,
    AxiIdWidthSlvPorts: AxiSystemIdWidth,
    AxiIdUsedSlvPorts : AxiSystemIdWidth,
    UniqueIds         : 0,
    AxiAddrWidth      : AddrWidth,
    AxiDataWidth      : DataWidth,
    NoAddrRules       : NumRules
  };

  /*********
   *  DUT  *
   *********/

  logic fetch_en;
  logic eoc_valid;

  mempool_system #(
    .TCDMBaseAddr(32'h0   ),
    .BootAddr    (BootAddr)
  ) dut (
    .clk_i          (clk            ),
    .rst_ni         (rst_n          ),
    .fetch_en_i     (fetch_en       ),
    .eoc_valid_o    (eoc_valid      ),
    .busy_o         (/*Unused*/     ),
    .mst_req_o      (axi_mst_req    ),
    .mst_resp_i     (axi_mst_resp   ),
    .slv_req_i      (to_mempool_req ),
    .slv_resp_o     (to_mempool_resp)
  );

  /**********************
   *  AXI Interconnect  *
   **********************/

  localparam addr_t UARTBaseAddr = 32'hC000_0000;
  localparam addr_t UARTEndAddr = 32'hC000_FFFF;

  xbar_rule_32_t [NumRules-1:0] xbar_routing_rules = '{
    '{idx: UART, start_addr: UARTBaseAddr, end_addr: UARTEndAddr}
  };

  axi_xbar #(
    .Cfg          (XBarCfg          ),
    .slv_aw_chan_t(axi_system_aw_t  ),
    .mst_aw_chan_t(axi_tb_aw_t      ),
    .w_chan_t     (axi_tb_w_t       ),
    .slv_b_chan_t (axi_system_b_t   ),
    .mst_b_chan_t (axi_tb_b_t       ),
    .slv_ar_chan_t(axi_system_ar_t  ),
    .mst_ar_chan_t(axi_tb_ar_t      ),
    .slv_r_chan_t (axi_system_r_t   ),
    .mst_r_chan_t (axi_tb_r_t       ),
    .slv_req_t    (axi_system_req_t ),
    .slv_resp_t   (axi_system_resp_t),
    .mst_req_t    (axi_tb_req_t     ),
    .mst_resp_t   (axi_tb_resp_t    ),
    .rule_t       (xbar_rule_32_t)
  ) i_testbench_xbar (
    .clk_i                (clk                  ),
    .rst_ni               (rst_n                ),
    .test_i               (1'b0                 ),
    .slv_ports_req_i      (axi_mst_req          ),
    .slv_ports_resp_o     (axi_mst_resp         ),
    .mst_ports_req_o      (axi_mem_req          ),
    .mst_ports_resp_i     (axi_mem_resp         ),
    .addr_map_i           (xbar_routing_rules   ),
    .en_default_mst_port_i('1                   ), // default all slave ports to master port Host
    .default_mst_port_i   ({NumAXIMasters{Host}})
  );

  /**********
   *  HOST  *
   **********/
  assign axi_mem_resp[Host] = '0;

  /**********
   *  UART  *
   **********/

  axi_uart #(
    .axi_req_t (axi_tb_req_t ),
    .axi_resp_t(axi_tb_resp_t)
  ) i_axi_uart (
    .clk_i     (clk               ),
    .rst_ni    (rst_n             ),
    .testmode_i(1'b0              ),
    .axi_req_i (axi_mem_req[UART] ),
    .axi_resp_o(axi_mem_resp[UART])
  );

  /*********
   *  WFI  *
   *********/

`ifndef TARGET_SYNTHESIS
`ifndef TARGET_VERILATOR
`ifndef POSTLAYOUT
`ifndef TRAFFIC_GEN

  // Helper debug signal with the wfi of each core
  logic [NumCores-1:0]          wfi;

  for (genvar g = 0; g < NumGroups; g++) begin: gen_wfi_groups
    for (genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_wfi_tiles
      for (genvar c = 0; c < NumCoresPerTile; c++) begin: gen_wfi_cores
        assign wfi[g*NumTilesPerGroup*NumCoresPerTile + t*NumCoresPerTile + c] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch.wfi_q;
      end: gen_wfi_cores
    end: gen_wfi_tiles
  end: gen_wfi_groups

`endif
`endif
`endif
`endif

  /************************
   *  Write/Read via AXI  *
   ************************/

  task write_to_mempool(input addr_t addr, input data_t data, output axi_pkg::resp_t resp);
    to_mempool_req.aw.id = 'h18d;
    to_mempool_req.aw.addr = addr;
    to_mempool_req.aw.size = 'h2;
    to_mempool_req.aw.burst = axi_pkg::BURST_INCR;
    to_mempool_req.aw_valid = 1'b1;
    `wait_for(to_mempool_resp.aw_ready)
    to_mempool_req.aw_valid = 1'b0;
    to_mempool_req.w.data = data << addr[ByteOffset +: $clog2(AxiDataWidth/DataWidth)] * DataWidth;
    to_mempool_req.w.strb = {BeWidth{1'b1}} << addr[ByteOffset +: $clog2(AxiDataWidth/DataWidth)] * BeWidth;
    to_mempool_req.w.last = 1'b1;
    to_mempool_req.w.user = '0;
    to_mempool_req.w_valid = 1'b1;
    `wait_for(to_mempool_resp.w_ready)
    to_mempool_req.w_valid = 1'b0;
    to_mempool_req.b_ready = 1'b1;
    `wait_for(to_mempool_resp.b_valid)
    resp = to_mempool_resp.b.resp;
    to_mempool_req.b_ready = 1'b0;
  endtask

  task read_from_mempool(input addr_t addr, output data_t data, output axi_pkg::resp_t resp);
    to_mempool_req.ar.id = 'h18d;
    to_mempool_req.ar.addr = addr;
    to_mempool_req.ar.size = 'h2;
    to_mempool_req.ar.burst = axi_pkg::BURST_INCR;
    to_mempool_req.ar_valid = 1'b1;
    `wait_for(to_mempool_resp.ar_ready)
    to_mempool_req.ar_valid = 1'b0;
    to_mempool_req.r_ready = 1'b1;
    `wait_for(to_mempool_resp.r_valid)
    data = to_mempool_resp.r.data >> addr[ByteOffset +: $clog2(AxiDataWidth/DataWidth)] * DataWidth;
    resp = to_mempool_resp.r.resp;
    to_mempool_req.r_ready = 1'b0;
    $display("[TB] Read %08x from %08x at %t (resp=%d).", data, addr, $time, resp);
  endtask

  axi_pkg::resp_t resp;

  // Simulation control
  initial begin
    localparam ctrl_phys_addr = 32'h4000_0000;
    localparam ctrl_size      = 32'h0100_0000;
    localparam l2_phys_addr   = 32'h8000_0000;
    localparam l2_size        = 32'h0700_0000;
    localparam ctrl_virt_addr = ctrl_phys_addr;
    localparam l2_virt_addr   = l2_phys_addr;
    addr_t first, last, phys_addr;
    data_t rdata;
    axi_pkg::resp_t resp;
    fetch_en = 1'b0;
    to_mempool_req = '{default: '0};
    to_mempool_req.aw.burst = axi_pkg::BURST_INCR;
    to_mempool_req.ar.burst = axi_pkg::BURST_INCR;
    to_mempool_req.aw.cache = axi_pkg::CACHE_MODIFIABLE;
    to_mempool_req.ar.cache = axi_pkg::CACHE_MODIFIABLE;
    // Wait for reset.
    wait (rst_n);
    @(posedge clk);

    // Give the cores time to execute the bootrom's program
    #(1000*ClockPeriod);

    // Wake up all cores
    write_to_mempool(ctrl_virt_addr + 32'h4, {DataWidth{1'b1}}, resp);
    assert(resp == axi_pkg::RESP_OKAY);

    if (PollEoc) begin
      // Poll for EOC (as done on the host at the moment)
      do begin
        #(1000*ClockPeriod);
        @(posedge clk);
        read_from_mempool(ctrl_virt_addr, rdata, resp);
        assert(resp == axi_pkg::RESP_OKAY);
      end while (rdata == 0);
    end else begin
      // Wait for the interrupt
      wait (eoc_valid);
      read_from_mempool(ctrl_virt_addr, rdata, resp);
      assert(resp == axi_pkg::RESP_OKAY);
    end
    $timeformat(-9, 2, " ns", 0);
    $display("[EOC] Simulation ended at %t (retval = %0d).", $time, rdata >> 1);
    $finish(0);
    // Start MemPool
    fetch_en = 1'b1;
  end

  /***********************
   *  L2 Initialization  *
   ***********************/

`ifndef DRAM
  for (genvar bank = 0; bank < NumL2Banks; bank++) begin : gen_l2_banks_init
    initial begin : l2_init
      automatic logic [L2BankWidth-1:0] mem_row;
      byte buffer [];
      addr_t address;
      addr_t length;
      string binary;

      // Initialize memories
      void'($value$plusargs("PRELOAD=%s", binary));
      if (binary != "") begin
        // Read ELF
        read_elf(binary);
        $display("Loading %s", binary);
        while (get_section(address, length)) begin
          // Read sections
          automatic int nwords = (length + L2BeWidth - 1)/L2BeWidth;
          $display("Loading section %x of length %x", address, length);
          buffer = new[nwords * L2BeWidth];
          void'(read_section(address, buffer));
          // Initializing memories
          for (int w = 0; w < nwords; w++) begin
            mem_row = '0;
            for (int b = 0; b < L2BankBeWidth; b++) begin
              mem_row[8 * b +: 8] = buffer[(bank + w * NumL2Banks) * L2BankBeWidth + b];
            end
            if (address >= dut.L2MemoryBaseAddr && address < dut.L2MemoryEndAddr) begin
              dut.gen_l2_banks[bank].l2_mem.init_val[(address - dut.L2MemoryBaseAddr + (w << L2ByteOffset)) >> L2ByteOffset] = mem_row;
            end else begin
              $display("Cannot initialize address %x, which doesn't fall into the L2 region.", address);
            end
          end
        end
      end
    end : l2_init
  end : gen_l2_banks_init

`else
  for (genvar bank = 0; bank < NumDrams; bank++) begin : gen_drams_init
    initial begin : l2_init
      automatic logic [L2BankWidth-1:0] mem_row;
      byte buffer [];
      addr_t address;
      addr_t length;
      string binary;
      // Initialize memories
      void'($value$plusargs("PRELOAD=%s", binary));
      if (binary != "") begin
        // Read ELF
        read_elf(binary);
        $display("Loading %s", binary);
        while (get_section(address, length)) begin
          // Read sections
          automatic int nwords = (length + L2DramBeWidth - 1)/L2DramBeWidth;
          $display("Loading section %x of length %x", address, length);
          buffer = new[nwords * L2DramBeWidth];
          void'(read_section(address, buffer));
          if (address >= dut.L2MemoryBaseAddr) begin
            for (int i = 0; i < nwords * L2DramBeWidth; i++) begin //per byte
              automatic dram_ctrl_interleave_t dram_ctrl_info;
              dram_ctrl_info = getDramCTRLInfo(address + i - dut.L2MemoryBaseAddr);
              if (dram_ctrl_info.dram_ctrl_id == bank) begin
                dut.gen_drams[bank].i_axi_dram_sim.i_sim_dram.load_a_byte_to_dram(dram_ctrl_info.dram_ctrl_addr, buffer[i]);
              end
            end
          end else begin
            $display("Cannot initialize address %x, which doesn't fall into the L2 DRAM region.", address);
          end
        end
      end
    end : l2_init
  end : gen_drams_init

`endif

  /**************************************
   *  MAC Utilization                   *
   **************************************/
`ifndef TARGET_SYNTHESIS
`ifndef TARGET_VERILATOR
`ifndef POSTLAYOUT

`ifndef TRAFFIC_GEN

  // Cores
  logic [NumCores-1:0] instruction_handshake, lsu_request, lsu_handshake;
  int unsigned snitch_utilization, lsu_pressure, lsu_utilization;
  assign snitch_utilization = $countones(instruction_handshake);
  assign lsu_utilization = $countones(lsu_handshake);
  assign lsu_pressure = $countones(lsu_request);

  for (genvar g = 0; g < NumGroups; g++) begin
    for (genvar t = 0; t < NumTilesPerGroup; t++) begin
      for (genvar c = 0; c < NumCoresPerTile; c++) begin
        logic valid_instr, stall;
        logic lsu_valid, lsu_ready;
        // Snitch
        assign valid_instr = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch.valid_instr;
        assign stall = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch.stall;
        assign instruction_handshake[g*NumTilesPerGroup*NumCoresPerTile+t*NumCoresPerTile+c] = valid_instr & !stall;
        // Interconnect
        assign lsu_valid = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch.data_qvalid_o;
        assign lsu_ready = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch.data_qready_i;
        assign lsu_request[g*NumTilesPerGroup*NumCoresPerTile+t*NumCoresPerTile+c] = lsu_valid & !lsu_ready;
        assign lsu_handshake[g*NumTilesPerGroup*NumCoresPerTile+t*NumCoresPerTile+c] = lsu_valid & lsu_ready;
      end
    end
  end

  // DSPU
  if (snitch_pkg::XPULPIMG) begin: gen_utilization
    logic [NumCores-1:0] dspu_handshake, dspu_mac;
    int unsigned dspu_utilization, mac_utilization;
    assign dspu_utilization = $countones(dspu_handshake);
    assign mac_utilization = $countones(dspu_mac);
    for (genvar g = 0; g < NumGroups; g++) begin
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin
        for (genvar c = 0; c < NumCoresPerTile; c++) begin
          logic dsp_valid, dsp_ready, mac;
          assign dsp_valid = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch_ipu.gen_xpulpimg.i_dspu.in_valid_i;
          assign dsp_ready = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch_ipu.gen_xpulpimg.i_dspu.in_ready_o;
          assign mac = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.gen_cores[c].gen_mempool_cc.riscv_core.i_snitch_ipu.gen_xpulpimg.i_dspu.operator_i ==? riscv_instr::P_MAC;
          assign dspu_handshake[g*NumTilesPerGroup*NumCoresPerTile+t*NumCoresPerTile+c] = dsp_valid & dsp_ready;
          assign dspu_mac[g*NumTilesPerGroup*NumCoresPerTile+t*NumCoresPerTile+c] = dsp_valid & dsp_ready & mac;
        end
      end
    end
  end

`endif

  // AXI
  logic [NumGroups*NumAXIMastersPerGroup-1:0] w_valid, w_ready, r_ready, r_valid;
  int unsigned axi_w_utilization, axi_r_utilization;
  assign axi_w_utilization = $countones(w_valid & w_ready);
  assign axi_r_utilization = $countones(r_ready & r_valid);
  for (genvar a = 0; a < NumGroups*NumAXIMastersPerGroup; a++) begin
    assign w_valid[a] = dut.i_mempool_cluster.axi_mst_req_o[a].w_valid;
    assign w_ready[a] = dut.i_mempool_cluster.axi_mst_resp_i[a].w_ready;
    assign r_ready[a] = dut.i_mempool_cluster.axi_mst_req_o[a].r_ready;
    assign r_valid[a] = dut.i_mempool_cluster.axi_mst_resp_i[a].r_valid;
  end

`endif
`endif
`endif


`ifndef TARGET_SYNTHESIS
`ifndef TARGET_VERILATOR
  logic [63:0] cycle_q;
  always_ff @(posedge clk or negedge rst_n) begin
    if(~rst_n) begin
      cycle_q   <= '0;
    end else begin
      cycle_q   <= cycle_q + 64'd1;
    end
  end

  // always_comb begin
  //   if(cycle_q > 3600)
  //     $finish;
  // end

`ifdef NOC_PROFILING
  int f_2, f_final_2;
  string fn_2, fn_final_2;
  int f_3, f_final_3;
  string fn_3, fn_final_3;
  int f_4, f_final_4;
  string fn_4, fn_final_4;
  string dump_time;
  int req_floo_input_log_fd;

  // string app;
  string log_path;
  integer retval;
  initial begin
    // void'($value$plusargs("APP=%s", app));
    // $sformat(log_path, "../scripts/spm_profiling/run_logs_remap_%1d/%s", NumCores, app);
    // $sformat(log_path, "../scripts/spm_profiling/run_logs_%1d/%s", NumCores, app);
    // $sformat(log_path, "../scripts/spm_profiling/run_logs_remap_f_%1d/%s", NumCores, app);
    // $sformat(log_path, "../scripts/spm_profiling/run_logs_f_%1d/%s", NumCores, app);
    $sformat(log_path, "noc_profiling");
    retval = $system({"mkdir -p ", log_path});
    req_floo_input_log_fd = $fopen($sformatf("%s/req_floo_input.log", log_path), "w");
  end

  tile_level_profile_t   tile_level_profile_d,   tile_level_profile_q  [NumGroups-1:0][NumTilesPerGroup-1:0]; 
  group_level_profile_t  group_level_profile_d,  group_level_profile_q [NumGroups-1:0];
  router_level_profile_t router_level_profile_d, router_level_profile_q[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][2-1:0]; // 2: req+rsp noc

  // tile level profiling
  generate
    for (genvar g = 0; g < NumGroups; g++) begin
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin
        always_ff @(posedge clk or negedge rst_n) begin
          if(!rst_n) begin
            for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
              tile_level_profile_q[g][t].req_vld_cyc_num[p] = '0;
              tile_level_profile_q[g][t].req_hsk_cyc_num[p] = '0;
            end
          end else begin
            for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
              tile_level_profile_q[g][t].req_vld_cyc_num[p] = tile_level_profile_q[g][t].req_vld_cyc_num[p] +
                                                              $countones(
                                                                dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.tcdm_master_req_valid_o[p+1]
                                                              );
              tile_level_profile_q[g][t].req_hsk_cyc_num[p] = tile_level_profile_q[g][t].req_hsk_cyc_num[p] +
                                                              $countones(
                                                                dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.tcdm_master_req_valid_o[p+1] &
                                                                dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.tcdm_master_req_ready_i[p+1]
                                                              );
              
            end
          end
        end
      end
    end
  endgenerate

  // group level profiling
  logic [NumGroups-1:0][NumTilesPerGroup*NumBanksPerTile-1:0][$clog2(NumTilesPerGroup*(NumRemotePortsPerTile-1)):0] group_xbar_req_to_same_bank_count;
  logic [NumGroups-1:0][NumTilesPerGroup*NumBanksPerTile-1:0][$clog2(NumTilesPerGroup*(NumRemotePortsPerTile-1)):0] group_xbar_req_to_same_bank_conflict_count;
  logic [NumGroups-1:0][$clog2(NumTilesPerGroup*(NumRemotePortsPerTile-1)):0] group_xbar_req_to_same_bank_conflict_count_sum;

  logic [NumX-1:0][NumY-1:0][NumRemotePortsPerTile-1-1:0][NumTilesPerGroup-1:0]                                                             tcdm_slave_req_valid;
  logic [NumX-1:0][NumY-1:0][NumRemotePortsPerTile-1-1:0][NumTilesPerGroup-1:0][idx_width(NumTilesPerGroup)+idx_width(NumBanksPerTile)-1:0] tcdm_slave_req_tgt_addr;

  generate
    for(genvar x_dim = 0; x_dim < NumX; x_dim++) begin
      for(genvar y_dim = 0; y_dim < NumY; y_dim++) begin
        for (genvar p = 0; p < (NumRemotePortsPerTile-1); p++) begin
          for(genvar t_i = 0; t_i < NumTilesPerGroup; t_i++) begin
            assign tcdm_slave_req_valid   [x_dim][y_dim][p][t_i] = dut.i_mempool_cluster.gen_groups_x[x_dim].gen_groups_y[y_dim].i_group.floo_req_from_router_before_xbar_valid_per_port[p+1][t_i];
            assign tcdm_slave_req_tgt_addr[x_dim][y_dim][p][t_i] = dut.i_mempool_cluster.gen_groups_x[x_dim].gen_groups_y[y_dim].i_group.floo_req_from_router[t_i][p+1].hdr.tgt_addr[idx_width(NumTilesPerGroup)+idx_width(NumBanksPerTile)-1:0];
          end
        end
      end
    end
  endgenerate

  always_comb begin
    group_xbar_req_to_same_bank_count = '0;
    for(int g = 0; g < NumGroups; g++) begin
      for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
        for(int t_i = 0; t_i < NumTilesPerGroup; t_i++) begin
          if(
            tcdm_slave_req_valid   [g/NumY][g%NumY][p][t_i] // if source port from router is valid
          ) begin
            group_xbar_req_to_same_bank_count[g][
              tcdm_slave_req_tgt_addr[g/NumY][g%NumY][p][t_i]
            ] += 1; // then destination port count +1
          end
        end
      end
    end
  end

  always_comb begin
    group_xbar_req_to_same_bank_conflict_count = '0;
    group_xbar_req_to_same_bank_conflict_count_sum = '0;
    for(int g = 0; g < NumGroups; g++) begin
      for(int b = 0; b < NumTilesPerGroup*NumBanksPerTile; b++) begin
        if(group_xbar_req_to_same_bank_count[g][b] > 0) begin
          group_xbar_req_to_same_bank_conflict_count[g][b] = group_xbar_req_to_same_bank_count[g][b] - 1; // minus the one that is not conflict.
        end
        group_xbar_req_to_same_bank_conflict_count_sum[g] += group_xbar_req_to_same_bank_conflict_count[g][b];
      end
    end
  end

  generate
    for (genvar g = 0; g < NumGroups; g++) begin
      always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
          for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
            group_level_profile_q[g].req_vld_cyc_num[p] = '0;
            group_level_profile_q[g].req_hsk_cyc_num[p] = '0;
          end
          group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num = '0;
        end else begin
          for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
            group_level_profile_q[g].req_vld_cyc_num[p]                             = group_level_profile_q[g].req_vld_cyc_num[p] +
                                                                                      $countones(
                                                                                        dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.floo_req_from_router_before_xbar_valid_per_port[p+1][NumTilesPerGroup-1:0]
                                                                                      );
            group_level_profile_q[g].req_hsk_cyc_num[p]                             = group_level_profile_q[g].req_hsk_cyc_num[p] +
                                                                                      $countones(
                                                                                        dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.floo_req_from_router_before_xbar_valid_per_port[p+1][NumTilesPerGroup-1:0] &
                                                                                        dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.floo_req_from_router_before_xbar_ready_per_port[p+1][NumTilesPerGroup-1:0]
                                                                                      );
          end
          group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num  = group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num +
                                                                                  group_xbar_req_to_same_bank_conflict_count_sum[g];
        end
      end
    end
  endgenerate

  // router level profiling
  generate
    for (genvar g = 0; g < NumGroups; g++) begin: gen_router_profile_per_group
      for(genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_router_profile_per_tile
        for(genvar p = 0; p < (NumRemotePortsPerTile-1); p++) begin: gen_router_profile_per_remote_port
          always_ff @(posedge clk or negedge rst_n) begin
            if(!rst_n) begin
              for(int router_p = 0; router_p < 4; router_p++) begin
                router_level_profile_q[g][t][p][0].in_vld_cyc_num[router_p] = '0;
                router_level_profile_q[g][t][p][0].in_hsk_cyc_num[router_p] = '0;
                router_level_profile_q[g][t][p][0].out_vld_cyc_num[router_p] = '0;
                router_level_profile_q[g][t][p][0].out_hsk_cyc_num[router_p] = '0;
                router_level_profile_q[g][t][p][1].in_vld_cyc_num[router_p] = '0;
                router_level_profile_q[g][t][p][1].in_hsk_cyc_num[router_p] = '0;
                router_level_profile_q[g][t][p][1].out_vld_cyc_num[router_p] = '0;
                router_level_profile_q[g][t][p][1].out_hsk_cyc_num[router_p] = '0;
              end
            end else begin
              for(int router_p = 0; router_p < 4; router_p++) begin
                // req router
                router_level_profile_q[g][t][p][0].in_vld_cyc_num[router_p]  = router_level_profile_q[g][t][p][0].in_vld_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_req_router.valid_i[router_p+1]
                                );
                router_level_profile_q[g][t][p][0].in_hsk_cyc_num[router_p]  = router_level_profile_q[g][t][p][0].in_hsk_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_req_router.valid_i[router_p+1] &
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_req_router.ready_o[router_p+1]
                                );
                router_level_profile_q[g][t][p][0].out_vld_cyc_num[router_p] = router_level_profile_q[g][t][p][0].out_vld_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_req_router.valid_o[router_p+1]
                                );
                router_level_profile_q[g][t][p][0].out_hsk_cyc_num[router_p] = router_level_profile_q[g][t][p][0].out_hsk_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_req_router.valid_o[router_p+1] &
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_req_router.ready_i[router_p+1]
                                );
                // resq router
                router_level_profile_q[g][t][p][1].in_vld_cyc_num[router_p]  = router_level_profile_q[g][t][p][1].in_vld_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_resp_router.valid_i[router_p+1]
                                );
                router_level_profile_q[g][t][p][1].in_hsk_cyc_num[router_p]  = router_level_profile_q[g][t][p][1].in_hsk_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_resp_router.valid_i[router_p+1] &
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_resp_router.ready_o[router_p+1]
                                );
                router_level_profile_q[g][t][p][1].out_vld_cyc_num[router_p] = router_level_profile_q[g][t][p][1].out_vld_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_resp_router.valid_o[router_p+1]
                                );
                router_level_profile_q[g][t][p][1].out_hsk_cyc_num[router_p] = router_level_profile_q[g][t][p][1].out_hsk_cyc_num[router_p] +
                                $countones(
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_resp_router.valid_o[router_p+1] &
                                  dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[p+1].i_floo_resp_router.ready_i[router_p+1]
                                );
              end
            end
          end
        end
      end
    end
  endgenerate


  always_ff @(posedge clk) begin
    if (rst_n) begin
      // if(cycle_q[19:0] == 'h80000) begin
      if(
          ((cycle_q[63:0] < 'h8000) && ((cycle_q[10:0] == 11'h400) || (cycle_q[10:0] == 11'h000))) ||
          (cycle_q[15:0] == 'h8000)
        ) begin

        $sformat(fn_2, "%s/tile_level_profile_q_%8x.log", log_path, cycle_q);
        f_2 = $fopen(fn_2, "w");
        $display("[Tracer] Final Logging Banks to %s", fn_2);

        $sformat(fn_3, "%s/group_level_profile_q_%8x.log", log_path, cycle_q);
        f_3 = $fopen(fn_3, "w");
        $display("[Tracer] Final Logging Banks to %s", fn_3);

        $sformat(fn_4, "%s/router_level_profile_q_%8x.log", log_path, cycle_q);
        f_4 = $fopen(fn_4, "w");
        $display("[Tracer] Final Logging Banks to %s", fn_4);

        $timeformat(-9, 0, "", 10);
        $sformat(dump_time, "dump time %t, cycle %8d #;\n", $time, cycle_q);
        $fwrite(f_2, dump_time);
        $fwrite(f_3, dump_time);
        $fwrite(f_4, dump_time);

        // tile level
        for(int g = 0; g < NumGroups; g++) begin
          for(int t_i = 0; t_i < NumTilesPerGroup; t_i++) begin
            for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
              automatic string extras_str_2;
              extras_str_2 = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, 'util': %.2f\n", 
                g, t_i, p,
                tile_level_profile_q[g][t_i].req_vld_cyc_num[p],
                tile_level_profile_q[g][t_i].req_hsk_cyc_num[p],
                (tile_level_profile_q[g][t_i].req_hsk_cyc_num[p]*1.0)/(tile_level_profile_q[g][t_i].req_vld_cyc_num[p]*1.0)
              );
              $fwrite(f_2, extras_str_2);
            end
          end
        end
        $fclose(f_2);

        // group level
        for(int g = 0; g < NumGroups; g++) begin
          int unsigned req_vld_cyc_num_sum;
          int unsigned req_hsk_cyc_num_sum;
          automatic string extras_str_3;
          req_vld_cyc_num_sum = 0;
          req_hsk_cyc_num_sum = 0;
          for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
            req_vld_cyc_num_sum += group_level_profile_q[g].req_vld_cyc_num[p];
            req_hsk_cyc_num_sum += group_level_profile_q[g].req_hsk_cyc_num[p];
          end
          extras_str_3 = $sformatf("{'GROUP': %03d, 'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, 'req_vld_cyc_more_than_one_hit_same_bank_num': %03d, 'util': %.2f\n", 
            g,
            req_vld_cyc_num_sum,
            req_hsk_cyc_num_sum,
            group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num,
            (req_hsk_cyc_num_sum*1.0)/((req_vld_cyc_num_sum-group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num)*1.0)
          );
          $fwrite(f_3, extras_str_3);
        end
        $fclose(f_3);

        // router level
        for(int g = 0; g < NumGroups; g++) begin
          for(int t = 0; t < NumTilesPerGroup; t++) begin
            for(int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
              for(int req_rsp = 0; req_rsp < 2; req_rsp++) begin
                for(int dir = 0; dir < 4; dir++) begin
                  automatic string extras_str_4;
                  extras_str_4 = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': %03d, 'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, 'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, 'in_util': %.2f, 'out_util': %.2f\n", 
                    g, t, p, req_rsp, dir,
                    router_level_profile_q[g][t][p][req_rsp].in_vld_cyc_num[dir],
                    router_level_profile_q[g][t][p][req_rsp].in_hsk_cyc_num[dir],
                    router_level_profile_q[g][t][p][req_rsp].out_vld_cyc_num[dir],
                    router_level_profile_q[g][t][p][req_rsp].out_hsk_cyc_num[dir],
                    router_level_profile_q[g][t][p][req_rsp].in_vld_cyc_num[dir]  > 0 ? (router_level_profile_q[g][t][p][req_rsp].in_hsk_cyc_num[dir]*1.0)/(router_level_profile_q[g][t][p][req_rsp].in_vld_cyc_num[dir]*1.0)   : 0,
                    router_level_profile_q[g][t][p][req_rsp].out_vld_cyc_num[dir] > 0 ? (router_level_profile_q[g][t][p][req_rsp].out_hsk_cyc_num[dir]*1.0)/(router_level_profile_q[g][t][p][req_rsp].out_vld_cyc_num[dir]*1.0) : 0
                  );
                  $fwrite(f_4, extras_str_4);
                end
              end
            end
          end
        end
        $fclose(f_4);
      end
    end
  end







  final begin
    $sformat(fn_final_2, "%s/tile_level_profile_q.log", log_path);
    f_final_2 = $fopen(fn_final_2, "w");
    $display("[Tracer] Final Logging Banks to %s", fn_final_2);

    $sformat(fn_final_3, "%s/group_level_profile_q.log", log_path);
    f_final_3 = $fopen(fn_final_3, "w");
    $display("[Tracer] Final Logging Banks to %s", fn_final_3);

    $sformat(fn_final_4, "%s/router_level_profile_q.log", log_path);
    f_final_4 = $fopen(fn_final_4, "w");
    $display("[Tracer] Final Logging Banks to %s", fn_final_4);

    $timeformat(-9, 0, "", 10);
    $sformat(dump_time, "dump time %t, cycle %8d #;\n", $time, cycle_q);
    $fwrite(f_final_2, dump_time);
    $fwrite(f_final_3, dump_time);
    $fwrite(f_final_4, dump_time);

    // tile level
    for(int g = 0; g < NumGroups; g++) begin
      for(int t_i = 0; t_i < NumTilesPerGroup; t_i++) begin
        for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
          automatic string extras_str_final_2;
          extras_str_final_2 = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, 'util': %.2f\n", 
            g, t_i, p,
            tile_level_profile_q[g][t_i].req_vld_cyc_num[p],
            tile_level_profile_q[g][t_i].req_hsk_cyc_num[p],
            (tile_level_profile_q[g][t_i].req_hsk_cyc_num[p]*1.0)/(tile_level_profile_q[g][t_i].req_vld_cyc_num[p]*1.0)
          );
          $fwrite(f_final_2, extras_str_final_2);
        end
      end
    end
    $fclose(f_final_2);

    // group level
    for(int g = 0; g < NumGroups; g++) begin
      int unsigned req_vld_cyc_num_sum;
      int unsigned req_hsk_cyc_num_sum;
      automatic string extras_str_final_3;
      req_vld_cyc_num_sum = 0;
      req_hsk_cyc_num_sum = 0;
      for (int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
        req_vld_cyc_num_sum += group_level_profile_q[g].req_vld_cyc_num[p];
        req_hsk_cyc_num_sum += group_level_profile_q[g].req_hsk_cyc_num[p];
      end
      extras_str_final_3 = $sformatf("{'GROUP': %03d, 'req_vld_cyc_num': %03d, 'req_hsk_cyc_num': %03d, 'req_vld_cyc_more_than_one_hit_same_bank_num': %03d, 'util': %.2f\n", 
        g,
        req_vld_cyc_num_sum,
        req_hsk_cyc_num_sum,
        group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num,
        (req_hsk_cyc_num_sum*1.0)/((req_vld_cyc_num_sum-group_level_profile_q[g].req_vld_cyc_more_than_one_hit_same_bank_num)*1.0)
      );
      $fwrite(f_final_3, extras_str_final_3);
    end
    $fclose(f_final_3);

    // router level
    for(int g = 0; g < NumGroups; g++) begin
      for(int t = 0; t < NumTilesPerGroup; t++) begin
        for(int p = 0; p < (NumRemotePortsPerTile-1); p++) begin
          for(int req_rsp = 0; req_rsp < 2; req_rsp++) begin
            for(int dir = 0; dir < 4; dir++) begin
              automatic string extras_str_final_4;
              extras_str_final_4 = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'REQ_RSP': %03d, 'DIR': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, 'out_vld_cyc_num': %03d, 'out_hsk_cyc_num': %03d, 'in_util': %.2f, 'out_util': %.2f\n", 
                g, t, p, req_rsp, dir,
                router_level_profile_q[g][t][p][req_rsp].in_vld_cyc_num[dir],
                router_level_profile_q[g][t][p][req_rsp].in_hsk_cyc_num[dir],
                router_level_profile_q[g][t][p][req_rsp].out_vld_cyc_num[dir],
                router_level_profile_q[g][t][p][req_rsp].out_hsk_cyc_num[dir],
                (router_level_profile_q[g][t][p][req_rsp].in_hsk_cyc_num[dir]*1.0)/(router_level_profile_q[g][t][p][req_rsp].in_vld_cyc_num[dir]*1.0),
                (router_level_profile_q[g][t][p][req_rsp].out_hsk_cyc_num[dir]*1.0)/(router_level_profile_q[g][t][p][req_rsp].out_vld_cyc_num[dir]*1.0)
              );
              $fwrite(f_final_4, extras_str_final_4);
            end
          end
        end
      end
    end
    $fclose(f_final_4);

  end

  floo_req_t floo_req_input_queue[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0][$];
  logic floo_req_input_fifo_ready_o[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  logic floo_req_input_fifo_valid_i[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  logic floo_req_input_fifo_ready_i[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  logic floo_req_input_fifo_valid_o[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  logic floo_req_output_fifo_ready_o[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  logic floo_req_output_fifo_valid_i[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  logic floo_req_output_fifo_ready_i[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  logic floo_req_output_fifo_valid_o[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  router_input_profile_t req_router_input_profile_q[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0];

  // logic floo_req_input_fifo_ready_o_dly[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  // logic floo_req_input_fifo_valid_i_dly[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  // logic floo_req_input_fifo_ready_i_dly[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];
  // logic floo_req_input_fifo_valid_o_dly[NumGroups-1:0][NumTilesPerGroup-1:0][(NumRemotePortsPerTile-1)-1:0][4:0];


  generate
    for(genvar g = 0; g < NumGroups; g++)  begin: gen_req_router_input_queue_per_group
      for(genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_req_router_input_queue_per_tile
        for(genvar r = 0; r < (NumRemotePortsPerTile-1); r++) begin: gen_req_router_input_queue_per_remote_port
          for(genvar router_p = 0; router_p < 5; router_p++) begin: gen_req_router_input_queue_per_dir
            assign floo_req_input_fifo_ready_o[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_input[router_p].gen_virt_input[0].i_stream_fifo.ready_o;
            assign floo_req_input_fifo_valid_i[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_input[router_p].gen_virt_input[0].i_stream_fifo.valid_i;
            assign floo_req_input_fifo_ready_i[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_input[router_p].gen_virt_input[0].i_stream_fifo.ready_i;
            assign floo_req_input_fifo_valid_o[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_input[router_p].gen_virt_input[0].i_stream_fifo.valid_o;
            assign floo_req_output_fifo_ready_o[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_output[router_p].gen_virt_output[0].gen_out_fifo.i_stream_fifo.ready_o;
            assign floo_req_output_fifo_valid_i[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_output[router_p].gen_virt_output[0].gen_out_fifo.i_stream_fifo.valid_i;
            assign floo_req_output_fifo_ready_i[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_output[router_p].gen_virt_output[0].gen_out_fifo.i_stream_fifo.ready_i;
            assign floo_req_output_fifo_valid_o[g][t][r][router_p] = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.gen_output[router_p].gen_virt_output[0].gen_out_fifo.i_stream_fifo.valid_o;
            
            // always_ff @(posedge clk) begin
            //   floo_req_input_fifo_ready_o_dly[g][t][r][router_p] = floo_req_input_fifo_ready_o[g][t][r][router_p];
            //   floo_req_input_fifo_valid_i_dly[g][t][r][router_p] = floo_req_input_fifo_valid_i[g][t][r][router_p];
            //   floo_req_input_fifo_ready_i_dly[g][t][r][router_p] = floo_req_input_fifo_ready_i[g][t][r][router_p];
            //   floo_req_input_fifo_valid_o_dly[g][t][r][router_p] = floo_req_input_fifo_valid_o[g][t][r][router_p];
            // end
            
            always_ff @(posedge clk) begin
              if (rst_n) begin
                if (floo_req_input_fifo_valid_i[g][t][r][router_p] & floo_req_input_fifo_ready_o[g][t][r][router_p]) begin
                  floo_req_input_queue[g][t][r][router_p].push_back(dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.gen_router_router_i[t].gen_router_router_j[r+1].i_floo_req_router.data_i[router_p]);
                end
                if (floo_req_input_fifo_valid_o[g][t][r][router_p] & floo_req_input_fifo_ready_i[g][t][r][router_p]) begin
                  floo_req_input_queue[g][t][r][router_p].delete(0);
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  function route_direction_e xy_routing (group_xy_id_t group_id, floo_req_t floo_req);
    automatic group_xy_id_t dest_id = group_xy_id_t'(floo_req.hdr.dst_id);
    if (dest_id == group_id) begin
      xy_routing = Eject;
    end else if (dest_id.x == group_id.x) begin
      if (dest_id.y < group_id.y) begin
        xy_routing = South;
      end else begin
        xy_routing = North;
      end
    end else begin
      if (dest_id.x < group_id.x) begin
        xy_routing = West;
      end else begin
        xy_routing = East;
      end
    end
  endfunction

  function group_xy_id_t get_next_hop (group_xy_id_t group_id, route_direction_e out_dir);
    if (out_dir == Eject) begin
      get_next_hop = group_id;
    end else if (out_dir == South) begin
      get_next_hop = '{x:group_id.x, y:group_id.y-1};
    end else if (out_dir == North) begin
      get_next_hop = '{x:group_id.x, y:group_id.y+1};
    end else if (out_dir == East) begin
      get_next_hop = '{x:group_id.x+1, y:group_id.y};
    end else if (out_dir == West) begin
      get_next_hop = '{x:group_id.x-1, y:group_id.y};
    end
  endfunction

  generate
    for(genvar g = 0; g < NumGroups; g++) begin: gen_req_router_input_profile_per_group
      for(genvar t = 0; t < NumTilesPerGroup; t++) begin: gen_req_router_input_profile_per_tile
        for(genvar r = 0; r < (NumRemotePortsPerTile-1); r++) begin: gen_req_router_input_profile_per_remote_port
          for(genvar router_p = 0; router_p < 5; router_p++) begin: gen_req_router_input_profile_per_dir
            always_ff @(posedge clk or negedge rst_n) begin
              if(!rst_n) begin
                req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p] = '0;
                req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p] = '0;
                req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p] = '0;
                req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p] = {'0, '0, '0, '0, '0};
                req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] = '0;
                req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p] = '0;
              end else begin
                if((cycle_q % 200) == 0) begin
                  req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p] = '0;
                  req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p] = '0;
                  req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p] = '0;
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p] = {'0, '0, '0, '0, '0};
                  req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p] = '0;
                end
                if(floo_req_input_fifo_valid_i[g][t][r][router_p]) begin
                  req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p] += 1;
                  if(floo_req_input_fifo_ready_o[g][t][r][router_p]) begin
                    req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p] += 1;
                    if(req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] > 0) begin
                      if(req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] > req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p]) begin
                        req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p] = req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p];
                        req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] = 0;
                      end
                    end
                  end else begin
                    assert(floo_req_input_fifo_valid_o[g][t][r][router_p]);
                    req_router_input_profile_q[g][t][r].cur_stall_cyc_num[router_p] += 1;
                    if(~floo_req_input_fifo_ready_i[g][t][r][router_p]) begin
                      automatic route_direction_e in_dir = route_direction_e'(router_p);
                      automatic route_direction_e out_dir = xy_routing(g, floo_req_input_queue[g][t][r][router_p][0]);
                      automatic group_xy_id_t cur_hop = g;
                      automatic logic cont = '1;
                      req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][out_dir] += 1;
                      assert(floo_req_output_fifo_valid_i[g][t][r][out_dir]);
                      while ('1) begin
                        for (int i = 1; i < floo_req_input_queue[cur_hop][t][r][in_dir].size(); i++) begin
                          out_dir = xy_routing(cur_hop, floo_req_input_queue[cur_hop][t][r][in_dir][i]);
                          if (~floo_req_output_fifo_valid_i[cur_hop][t][r][out_dir] & floo_req_output_fifo_ready_o[cur_hop][t][r][out_dir]) begin
                            req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p] += 1;
                            cont = '0;
                            break;
                          end
                        end
                        if (~cont) begin
                            break;
                          end
                        out_dir = xy_routing(cur_hop, floo_req_input_queue[cur_hop][t][r][in_dir][0]);
                        assert(floo_req_output_fifo_valid_i[cur_hop][t][r][out_dir]);
                        if (floo_req_output_fifo_ready_o[cur_hop][t][r][out_dir] | floo_req_output_fifo_ready_i[cur_hop][t][r][out_dir]) begin
                            break;
                          end
                        if (out_dir == Eject) begin
                            break;
                          end
                        cur_hop = get_next_hop(cur_hop, out_dir);
                        if (out_dir == North) begin
                          in_dir = South;
                        end else if (out_dir == South) begin
                          in_dir = North;
                        end else if (out_dir == East) begin
                          in_dir = West;
                        end else if (out_dir == West) begin
                          in_dir = East;
                        end
                        if (floo_req_input_fifo_ready_i[cur_hop][t][r][in_dir]) begin
                            break;
                          end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  always_ff @(negedge clk) begin: log_req_router_input_profile
    if(rst_n) begin
      for(int g = 0; g < NumGroups; g++) begin
        for(int t = 0; t < NumTilesPerGroup; t++) begin
          for(int r = 0; r < (NumRemotePortsPerTile-1); r++) begin
            for(int router_p = 0; router_p < 5; router_p++) begin
              if((cycle_q % 200) == 199) begin
                automatic string log_str;
                log_str = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'DIR': %03d, 'start_cycle': %03d, 'end_cycle': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, 'hol_stall_cyc_num': %03d, 'max_stall_cyc_num': %03d, 'out_dir0_cong_cyc_num': %03d, 'out_dir1_cong_cyc_num': %03d, 'out_dir2_cong_cyc_num': %03d, 'out_dir3_cong_cyc_num': %03d, 'out_dir4_cong_cyc_num': %03d}\n",
                  g, t, r, router_p, cycle_q-199, cycle_q,
                  req_router_input_profile_q[g][t][r].in_vld_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].max_stall_cyc_num[router_p],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][0],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][1],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][2],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][3],
                  req_router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][4]);
                $fwrite(req_floo_input_log_fd, log_str);
              end
            end
          end
        end
      end
    end
  end
                        end else begin
                          $fatal("Invalid next_hop");
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  always_ff @(negedge clk) begin: log_router_input_profile
    if(rst_n) begin
      for(int g = 0; g < NumGroups; g++) begin
        for(int t = 0; t < NumTilesPerGroup; t++) begin
          for(int r = 0; r < (NumRemotePortsPerTile-1); r++) begin
            for(int router_p = 0; router_p < 5; router_p++) begin
              if((cycle_q % 200) == 199) begin
                automatic string log_str;
                log_str = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'PORT': %03d, 'DIR': %03d, 'start_cycle': %03d, 'end_cycle': %03d, 'in_vld_cyc_num': %03d, 'in_hsk_cyc_num': %03d, 'hol_stall_cyc_num': %03d, 'max_stall_cyc_num': %03d, 'out_dir0_cong_cyc_num': %03d, 'out_dir1_cong_cyc_num': %03d, 'out_dir2_cong_cyc_num': %03d, 'out_dir3_cong_cyc_num': %03d, 'out_dir4_cong_cyc_num': %03d}\n",
                  g, t, r, router_p, cycle_q-199, cycle_q,
                  router_input_profile_q[g][t][r].in_vld_cyc_num[router_p],
                  router_input_profile_q[g][t][r].in_hsk_cyc_num[router_p],
                  router_input_profile_q[g][t][r].hol_stall_cyc_num[router_p],
                  router_input_profile_q[g][t][r].max_stall_cyc_num[router_p],
                  router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][0],
                  router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][1],
                  router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][2],
                  router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][3],
                  router_input_profile_q[g][t][r].out_congst_cyc_num[router_p][4]);
                $fwrite(floo_input_log_fd, log_str);
              end
            end
          end
        end
      end
    end
  end

`endif

`ifdef SPM_PROFILING
  int f_0, f_final_0;
  int f_1, f_final_1;
  string fn_0, fn_final_0;
  string fn_1, fn_final_1;

  string app;
  string log_path;
  initial begin
    void'($value$plusargs("APP=%s", app));
    $sformat(log_path, "../scripts/spm_profiling/run_logs/%s", app);
  end


  profile_t dbg_profile_q[NumGroups-1:0][NumTilesPerGroup-1:0][NumBanksPerTile-1:0][2**TCDMAddrMemWidth-1:0];

  generate
    for (genvar g = 0; g < NumGroups; g++) begin
      for (genvar t = 0; t < NumTilesPerGroup; t++) begin
        for (genvar b = 0; b < NumBanksPerTile; b++) begin
          for(genvar i = 0; i < 2**TCDMAddrMemWidth; i++) begin
            always_ff @(posedge clk or posedge rst_n) begin
              if(cycle_q[7:0] == 'h80) begin
                dbg_profile_q[g][t][b][i].initiated            = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].initiated;
                dbg_profile_q[g][t][b][i].initial_cycle        = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].initial_cycle;
                dbg_profile_q[g][t][b][i].last_read_cycle      = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].last_read_cycle;
                dbg_profile_q[g][t][b][i].last_write_cycle     = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].last_write_cycle;
                dbg_profile_q[g][t][b][i].last_access_cycle    = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].last_access_cycle;
                dbg_profile_q[g][t][b][i].access_read_number   = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].access_read_number;
                dbg_profile_q[g][t][b][i].access_write_number  = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].access_write_number;
                dbg_profile_q[g][t][b][i].access_number        = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].access_number;
                dbg_profile_q[g][t][b][i].read_cycles          = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].read_cycles;
                dbg_profile_q[g][t][b][i].write_cycles         = dut.i_mempool_cluster.gen_groups_x[g/NumY].gen_groups_y[g%NumY].i_group.i_mempool_group.gen_tiles[t].i_tile.profile_d[b][i].write_cycles;
              end
            end
          end
        end
      end
    end
  endgenerate


  always_ff @(posedge clk or posedge rst_n) begin
    if (rst_n) begin
      // if(cycle_q[19:0] == 'h80000) begin
      if((cycle_q[63:0] == 'h100) || 
        (cycle_q[63:0] == 'h200) || 
        (cycle_q[63:0] == 'h400) || 
        (cycle_q[63:0] == 'h800) ||
        (cycle_q[63:0] == 'h1000) ||
        (cycle_q[15:0] == 'h8000)) begin
      // if(cycle_q[8:0] == 'h100) begin
        $sformat(fn_0, "%s/trace_banks_cyc_%8x.dasm", log_path, cycle_q);
        // f_0 = $fopen(fn_0, "w");
        $sformat(fn_1, "%s/trace_banks_cyc_%8x_inited.dasm", log_path, cycle_q);
        f_1 = $fopen(fn_1, "w");
        $display("[Tracer] Logging Banks to %s, %s", fn_0, fn_1);

        for (int g = 0; g < NumGroups; g++) begin
          // extras_str = $sformatf("%s\n\n\n[GROUP %03d]", extras_str, g);
          for (int t = 0; t < NumTilesPerGroup; t++) begin
            // extras_str = $sformatf("%s\n> [GROUP %03d, TILE %03d]", extras_str, g, t);          
            for (int b = 0; b < NumBanksPerTile; b++) begin
              // extras_str = $sformatf("%s\n>> [GROUP %03d, TILE %03d, BANK %03d]", extras_str, g, t, b);          
              for(int i = 0; i < 2**TCDMAddrMemWidth; i++) begin
                automatic string trace_entry;
                automatic string extras_str;
                extras_str = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'BANK': %03d, 'IDX': 0x%x, 'inited': %03d, 'ini_cyc': %03d, 'last_rd_cyc': %03d, 'last_wr_cyc': %03d, 'last_acc_cyc': %03d, 'acc_rd_num': %03d, 'acc_wr_num': %03d, 'acc_num': %03d, ", 
                  g, t, b, i,
                  dbg_profile_q[g][t][b][i].initiated,
                  dbg_profile_q[g][t][b][i].initial_cycle,
                  dbg_profile_q[g][t][b][i].last_read_cycle,
                  dbg_profile_q[g][t][b][i].last_write_cycle,
                  dbg_profile_q[g][t][b][i].last_access_cycle,
                  dbg_profile_q[g][t][b][i].access_read_number,
                  dbg_profile_q[g][t][b][i].access_write_number,
                  dbg_profile_q[g][t][b][i].access_number
                );
                // read cycles
                extras_str = $sformatf("%s'rd_cyc': ", extras_str);
                foreach (dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]) begin
                  extras_str = $sformatf("%s%03d ", extras_str, dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]);
                end
                extras_str = $sformatf("%s, ", extras_str);
                // write cycles
                extras_str = $sformatf("%s'wr_cyc': ", extras_str);
                foreach (dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]) begin
                  extras_str = $sformatf("%s%03d ", extras_str, dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]);
                end
                extras_str = $sformatf("%s}", extras_str);
                // $timeformat(-9, 0, "", 10);
                // $sformat(trace_entry, "%t %8d #; %s\n",
                //     $time, cycle_q, extras_str);
                if(dbg_profile_q[g][t][b][i].initiated) begin
                  $sformat(trace_entry, "%8d #; %s\n",
                      cycle_q, extras_str);
                  $fwrite(f_1, trace_entry);
                end
                $sformat(trace_entry, "%8d #; %s\n",
                    cycle_q, extras_str);
                // $fwrite(f_0, trace_entry);
              end
            end
          end
        end
        // $fclose(f_0);
        $fclose(f_1);
      end
    end
  end


  final begin
    $sformat(fn_final_0, "%s/trace_banks_cyc_%8x_final.dasm", log_path, cycle_q);
    f_final_0 = $fopen(fn_final_0, "w");
    $sformat(fn_final_1, "%s/trace_banks_cyc_%8x_inited_final.dasm", log_path, cycle_q);
    f_final_1 = $fopen(fn_final_1, "w");
    $display("[Tracer] Final Logging Banks to %s, %s", fn_final_0, f_final_1);

    for (int g = 0; g < NumGroups; g++) begin
      for (int t = 0; t < NumTilesPerGroup; t++) begin
        for (int b = 0; b < NumBanksPerTile; b++) begin
          for(int i = 0; i < 2**TCDMAddrMemWidth; i++) begin
            automatic string trace_entry_final;
            automatic string extras_str_final;
            extras_str_final = $sformatf("{'GROUP': %03d, 'TILE': %03d, 'BANK': %03d, 'IDX': 0x%x, 'inited': %03d, 'ini_cyc': %03d, 'last_rd_cyc': %03d, 'last_wr_cyc': %03d, 'last_acc_cyc': %03d, 'acc_rd_num': %03d, 'acc_wr_num': %03d, 'acc_num': %03d, ", 
              g, t, b, i,
              dbg_profile_q[g][t][b][i].initiated,
              dbg_profile_q[g][t][b][i].initial_cycle,
              dbg_profile_q[g][t][b][i].last_read_cycle,
              dbg_profile_q[g][t][b][i].last_write_cycle,
              dbg_profile_q[g][t][b][i].last_access_cycle,
              dbg_profile_q[g][t][b][i].access_read_number,
              dbg_profile_q[g][t][b][i].access_write_number,
              dbg_profile_q[g][t][b][i].access_number
            );
            // read cycles
            extras_str_final = $sformatf("%s'rd_cyc': ", extras_str_final);
            foreach (dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]) begin
              extras_str_final = $sformatf("%s%03d ", extras_str_final, dbg_profile_q[g][t][b][i].read_cycles[cycle_idx]);
            end
            extras_str_final = $sformatf("%s, ", extras_str_final);
            // write cycles
            extras_str_final = $sformatf("%s'wr_cyc': ", extras_str_final);
            foreach (dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]) begin
              extras_str_final = $sformatf("%s%03d ", extras_str_final, dbg_profile_q[g][t][b][i].write_cycles[cycle_idx]);
            end
            extras_str_final = $sformatf("%s}", extras_str_final);
            // $timeformat(-9, 0, "", 10);
            if(dbg_profile_q[g][t][b][i].initiated) begin
              $sformat(trace_entry_final, "%8d #; %s\n",
                  cycle_q, extras_str_final);
              $fwrite(f_final_1, trace_entry_final);
            end
            $sformat(trace_entry_final, "%8d #; %s\n",
                cycle_q, extras_str_final);
            $fwrite(f_final_0, trace_entry_final);
          end
        end
      end
    end
    $fclose(f_final_0);
    $fclose(f_final_1);
  end
`endif
`endif
`endif

endmodule : mempool_tb
