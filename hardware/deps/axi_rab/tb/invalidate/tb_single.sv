`include "pulp_soc_defines.sv"
`include "utils.sv"

module tb_single;
  localparam AW = 32;
  localparam DW = 32;
  localparam SIW = 6;
  localparam MIW = 10;
  localparam UW = 8;
  localparam CK = 1ns;
  localparam TA = CK * 1 / 4;
  localparam TT = CK * 3 / 4;

  logic clk;
  int   clk_cnt;
  logic start;
  logic done = 0;

  AXI_BUS_DV
    #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(SIW),
      .AXI_USER_WIDTH(UW)
      ) axi_slave_dv(clk);

  AXI_BUS_DV
    #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(MIW),
      .AXI_USER_WIDTH(UW)
      ) axi_master_dv(clk);

  AXI_LITE_DV
    #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
      ) axi_config_dv(clk);

  base_tb
    #(
      .AW(AW),
      .DW(DW),
      .SIW(SIW),
      .MIW(MIW),
      .UW(UW),
      .CK(CK),
      .TA(TA),
      .TT(TT)
      )
  i_base_tb
    (
     .master_dv_in(axi_master_dv),
     .slave_dv_out(axi_slave_dv),
     .config_dv_in(axi_config_dv),
     .done_i(done),
     .start_o(start),
     .clk_o(clk),
     .clk_cnt_o(clk_cnt)
     );

  axi_lite_driver #(.AW(AW), .DW(DW), .TT(TT), .TA(TA)) axi_config_drv = new(axi_config_dv);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(SIW), .UW(UW), .TA(TA), .TT(TT)) axi_slave_drv = new(axi_slave_dv);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(MIW), .UW(UW), .TA(TA), .TT(TT)) axi_master_drv = new(axi_master_dv);

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(MIW), .UW(UW)) ax_beat = new;
    automatic axi_test::axi_r_beat  #(.DW(DW), .IW(MIW), .UW(UW)) r_beat = new;

    localparam integer N_SLICES_ARRAY[`RAB_N_PORTS-1:0] = `N_SLICES_ARRAY;
    localparam integer EN_L2TLB_ARRAY[`RAB_N_PORTS-1:0] = `EN_L2TLB_ARRAY;

    automatic int address, l1_va, max_va, va, pa;
    automatic int start_time, min_time = 1000000, max_time = 0;

    // NOTE: testbench currently assumes N_PORTS == 2 and L2 only on port 1 enabled
    assert(`RAB_N_PORTS == 2 && EN_L2TLB_ARRAY[0] == 0 && EN_L2TLB_ARRAY[1] == 1);
    axi_master_drv.reset_master();
    axi_config_drv.reset_master();
    @(posedge start);

    $display("Inserting entries...");
    // write L2 configuration (only accelerator -> host)
    for(int i=0; i<`RAB_L2_N_SET_ENTRIES; ++i) begin
      for(int j=0; j<`RAB_L2_N_SETS; ++j) begin
        address = 32'h8000 + j*4*`RAB_L2_N_SET_ENTRIES + i*4;
        pa      = 32'hff000000 + va;
        axi_config_drv.write_ok(address, (va >> 8) | 32'h7);
        axi_config_drv.write_ok(address + 32'h1000, (pa >> 12));
        va     += `PAGE_SIZE;
      end
    end
    l1_va = va;
    // write L1 configuration (only accelerator -> host)
    for(int i=0; i<N_SLICES_ARRAY[1]; ++i) begin
      address  = (N_SLICES_ARRAY[0]+1)*8'h20 + i*8'h20;
      pa       = 32'hff000000 + va;
      axi_config_drv.write_ok(address + 32'h00, va);
      axi_config_drv.write_ok(address + 32'h08, va+`PAGE_SIZE-1);
      axi_config_drv.write_ok(address + 32'h10, pa);
      axi_config_drv.write_ok(address + 32'h18, 3'b111);
      va      += `PAGE_SIZE;
    end
    max_va = va;

    $display("Checking entries...");
    // loop over addresses and remove and reinsert them
    for(int addr=0; addr<max_va; addr+=`PAGE_SIZE) begin
      // check current
      ax_beat.ax_addr = addr;
      ax_beat.ax_size = 3'b101;
      axi_master_drv.send_ar(ax_beat);
      axi_master_drv.recv_r(r_beat);
      if(r_beat.r_resp != 2'b00) begin
        $error("Expected 0x%08x to hit", addr);
      end else if(r_beat.r_data != 32'hff000000 + addr) begin
        $error("Hit for 0x%08x expected at 0x%08x instead of 0x%08x", addr, 32'hff000000 + addr, r_beat.r_data);
      end

      // invalidate
      axi_config_drv.write_ok(32'h10, addr);
      start_time = clk_cnt;
      axi_config_drv.write_ok(32'h18, addr+`PAGE_SIZE-1);
      if(clk_cnt - start_time > max_time) max_time = clk_cnt - start_time;
      if(clk_cnt - start_time < min_time) min_time = clk_cnt - start_time;

      // check current
      ax_beat.ax_addr = addr;
      ax_beat.ax_size = 3'b101;
      axi_master_drv.send_ar(ax_beat);
      axi_master_drv.recv_r(r_beat);
      if(r_beat.r_resp == 2'b00) begin
        $error("Expected 0x%08x to miss as entry has been invalidated", addr);
      end
      // check previous
      if(addr != 0) begin
        ax_beat.ax_addr = addr - 8'h40;
        ax_beat.ax_size = 3'b101;
        axi_master_drv.send_ar(ax_beat);
        axi_master_drv.recv_r(r_beat);
        if(r_beat.r_resp != 2'b00) begin
          $error("Expected address previous to 0x%08x to still hit", addr);
        end
      end
      // reinsert
      va = addr;
      pa = 32'hff000000 + va;
      if(addr >= l1_va) begin
        address = (N_SLICES_ARRAY[0]+1)*8'h20 + ((va-l1_va)/`PAGE_SIZE)*8'h20;
        axi_config_drv.write_ok(address + 32'h00, va);
        axi_config_drv.write_ok(address + 32'h08, va+`PAGE_SIZE-1);
        axi_config_drv.write_ok(address + 32'h10, pa);
        axi_config_drv.write_ok(address + 32'h18, 3'b111);
      end else begin
        address = 32'h8000 + ((va/`PAGE_SIZE)%`RAB_L2_N_SETS)*4*`RAB_L2_N_SET_ENTRIES + ((va/`PAGE_SIZE)/`RAB_L2_N_SETS)*4;
        axi_config_drv.write_ok(address, (va >> 8) | 32'h7);
        axi_config_drv.write_ok(address + 32'h1000, (pa >> 12));
      end
    end
    $display("Invalidation took between %d and %d cycles", min_time, max_time);

    $display("Success!");
    done = 1;
  end

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(SIW), .UW(UW)) ax_beat;
    automatic axi_test::axi_r_beat #(.DW(DW), .IW(SIW), .UW(UW)) r_beat = new;
    axi_slave_drv.reset_slave();

    // slave just sends back the rewritten address to the master
    while(1) begin
      axi_slave_drv.recv_ar(ax_beat);
      r_beat.r_id = ax_beat.ax_id;
      r_beat.r_data = ax_beat.ax_addr;
      r_beat.r_last = 1'b1;
      axi_slave_drv.send_r(r_beat);
    end
  end
endmodule
