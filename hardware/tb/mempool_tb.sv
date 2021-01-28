// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

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
  import axi_pkg::xbar_cfg_t;
  import axi_pkg::xbar_rule_32_t;

  `ifdef NUM_CORES
  localparam NumCores = `NUM_CORES;
  `else
  localparam NumCores = 256;
  `endif

  `ifdef BOOT_ADDR
  localparam BootAddr = `BOOT_ADDR;
  `else
  localparam BootAddr = 0;
  `endif

  localparam        BankingFactor    = 4;
  localparam addr_t TCDMBaseAddr     = '0;
  localparam        TCDMSizePerBank  = 1024 /* [B] */;
  localparam        NumTiles         = NumCores / NumCoresPerTile;
  localparam        NumTilesPerGroup = NumTiles / NumGroups;
  localparam        NumBanks         = NumCores * BankingFactor;
  localparam        TCDMSize         = NumBanks * TCDMSizePerBank;

  localparam ClockPeriod = 1ns;
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
  axi_lite_slv_req_t                        rab_conf_req;
  axi_lite_slv_resp_t                       rab_conf_resp;

  axi_system_req_t                          to_mempool_req;
  axi_system_resp_t                         to_mempool_resp;

  localparam xbar_cfg_t XBarCfg = '{
    NoSlvPorts        : NumAXIMasters,
    NoMstPorts        : NumAXISlaves,
    MaxMstTrans       : 4,
    MaxSlvTrans       : 4,
    FallThrough       : 1'b0,
    LatencyMode       : axi_pkg::CUT_MST_PORTS,
    AxiIdWidthSlvPorts: AxiSystemIdWidth,
    AxiIdUsedSlvPorts : AxiSystemIdWidth,
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
    .NumCores       (NumCores       ),
    .BankingFactor  (BankingFactor  ),
    .TCDMBaseAddr   (TCDMBaseAddr   ),
    .BootAddr       (BootAddr       )
  ) dut (
    .clk_i          (clk            ),
    .rst_ni         (rst_n          ),
    .fetch_en_i     (fetch_en       ),
    .eoc_valid_o    (eoc_valid      ),
    .busy_o         (/*Unused*/     ),
    .mst_req_o      (axi_mst_req    ),
    .mst_resp_i     (axi_mst_resp   ),
    .slv_req_i      (to_mempool_req ),
    .slv_resp_o     (to_mempool_resp),
    .rab_conf_req_i (rab_conf_req   ),
    .rab_conf_resp_o(rab_conf_resp  )
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

  // Printing
  axi_system_id_t id_queue [$];

  initial begin
    automatic string sb = "";

    axi_mem_resp[UART] <= '0;
    while (1) begin
      @(posedge clk); #TT;
      fork
        begin
          wait(axi_mem_req[UART].aw_valid);
          axi_mem_resp[UART].aw_ready <= 1'b1;
          axi_mem_resp[UART].aw_ready <= @(posedge clk) 1'b0;
          id_queue.push_back(axi_mem_req[UART].aw.id);
        end
        begin
          wait(axi_mem_req[UART].w_valid);
          axi_mem_resp[UART].w_ready <= 1'b1;
          axi_mem_resp[UART].w_ready <= @(posedge clk) 1'b0;
          $write("%c", axi_mem_req[UART].w.data);
        end
      join

      // Send response
      axi_mem_resp[UART].b_valid = 1'b1;
      axi_mem_resp[UART].b.id    = id_queue.pop_front();
      axi_mem_resp[UART].b.resp  = axi_pkg::RESP_OKAY;
      axi_mem_resp[UART].b.user  = '0;
      wait(axi_mem_req[UART].b_ready);
      @(posedge clk);
      axi_mem_resp[UART].b_valid = 1'b0;
    end
  end

  /*******************
   *  Configure RAB  *
   *******************/

  task write_rab(input addr_t addr, input axi_lite_data_t data);
    rab_conf_req.aw.addr = addr;
    rab_conf_req.aw_valid = 1'b1;
    `wait_for(rab_conf_resp.aw_ready)
    rab_conf_req.aw_valid = 1'b0;
    rab_conf_req.w.data = data;
    rab_conf_req.w.strb = '1;
    rab_conf_req.w_valid = 1'b1;
    `wait_for(rab_conf_resp.w_ready)
    rab_conf_req.w_valid = 1'b0;
    rab_conf_req.b_ready = 1'b1;
    `wait_for(rab_conf_resp.b_valid)
    rab_conf_req.b_ready = 1'b0;
  endtask

  task write_rab_slice(input addr_t slice_addr, input addr_t first, input addr_t last, input addr_t phys_addr);
    write_rab(slice_addr+8'h00, first);
    write_rab(slice_addr+8'h08, last);
    write_rab(slice_addr+8'h10, phys_addr);
    write_rab(slice_addr+8'h18, 32'h7);
  endtask

  task read_rab(input addr_t addr, output axi_lite_data_t data, output axi_pkg::resp_t resp);
    rab_conf_req.ar.addr = addr;
    rab_conf_req.ar_valid = 1'b1;
    `wait_for(rab_conf_resp.ar_ready)
    rab_conf_req.ar_valid = 1'b0;
    rab_conf_req.r_ready = 1'b1;
    `wait_for(rab_conf_resp.r_valid)
    resp = rab_conf_resp.r.resp;
    data = rab_conf_resp.r.data;
    rab_conf_req.r_ready = 1'b0;
    $display("[TB] Read %08x from %08x at %t (resp=%d).", data, addr, $time, resp);
  endtask

  task read_rab_slice(input addr_t slice_addr, output addr_t first, output addr_t last, output addr_t phys_addr, output addr_t rab_config);
    axi_pkg::resp_t resp;
    read_rab(slice_addr+8'h00, first, resp);
    read_rab(slice_addr+8'h08, last, resp);
    read_rab(slice_addr+8'h10, phys_addr, resp);
    read_rab(slice_addr+8'h18, rab_config, resp);
  endtask

  task write_to_mempool(input addr_t addr, input data_t data, output axi_pkg::resp_t resp);
    to_mempool_req.aw.id = 'h18d;
    to_mempool_req.aw.addr = addr;
    to_mempool_req.aw.size = 'h2;
    to_mempool_req.aw.burst = axi_pkg::BURST_INCR;
    to_mempool_req.aw_valid = 1'b1;
    `wait_for(to_mempool_resp.aw_ready)
    to_mempool_req.aw_valid = 1'b0;
    to_mempool_req.w.data = data << addr[ByteOffset +: (AxiDataWidth/DataWidth)] * DataWidth;
    to_mempool_req.w.strb = {BeWidth{1'b1}} << addr[ByteOffset +: (AxiDataWidth/DataWidth)] * BeWidth;
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
    data = to_mempool_resp.r.data >> addr[ByteOffset +: (AxiDataWidth/DataWidth)] * DataWidth;
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
`ifdef TARGET_FPGA
    localparam ctrl_virt_addr = 32'hA700_0000;
    localparam l2_virt_addr   = 32'hA000_0000;
`else
    localparam ctrl_virt_addr = ctrl_phys_addr;
    localparam l2_virt_addr   = l2_phys_addr;
`endif
    addr_t first, last, phys_addr, rab_config;
    data_t rdata;
    axi_pkg::resp_t resp;
    fetch_en = 1'b0;
    rab_conf_req = '{default: '0};
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

`ifdef TARGET_FPGA
    // Set up RAB slice from MemPool to the external devices
    // RAB is at 0xA800_0000 from the hosts perspective
    // MemPool is at 0xA000_0000 from the hosts perspective (then translated by RAB)
    write_rab_slice(32'hA80000A0, 32'h0000_1000, 32'hFFFF_FFFF, 32'h0000_1000);
    read_rab_slice(32'hA80000A0, first, last, phys_addr, rab_config);

    // Set up RAB slice from external/Host to  the L2 memory
    write_rab_slice(32'hA8000040, l2_virt_addr, l2_virt_addr+l2_size-1, l2_phys_addr);
    read_rab_slice(32'hA8000040, first, last, phys_addr, rab_config);

    // Set up RAB slice from external/Host to  the control registers
    write_rab_slice(32'hA8000060, ctrl_virt_addr, ctrl_virt_addr+ctrl_size-1, ctrl_phys_addr);
    read_rab_slice(32'hA8000060, first, last, phys_addr, rab_config);
`endif
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

  initial begin : l2_init
    automatic axi_data_t mem_row;
    byte buffer [];
    addr_t address;
    addr_t length;
    string binary;

    // Initialize memories
    void'($value$plusargs("PRELOAD=%s", binary));
    if (binary != "") begin
      // Read ELF
      void'(read_elf(binary));
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
          for (int b = 0; b < L2BeWidth; b++) begin
            mem_row[8 * b +: 8] = buffer[w * L2BeWidth + b];
          end
          if (address >= dut.L2MemoryBaseAddr && address < dut.L2MemoryEndAddr)
            dut.l2_mem.init_val[(address - dut.L2MemoryBaseAddr + (w << L2ByteOffset)) >> L2ByteOffset] = mem_row;
          else
            $display("Cannot initialize address %x, which doesn't fall into the L2 region.", address);
        end
      end
    end
  end : l2_init

endmodule : mempool_tb
