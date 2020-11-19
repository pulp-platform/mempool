`include "pulp_soc_defines.sv"
`include "utils.sv"

`define VERBOSE

module tb_random;
  timeunit 1ps;
  timeprecision 1ps;

  localparam AW = 32;
  localparam DW = 32;
  localparam SIW = 6;
  localparam MIW = 10;
  localparam UW = 8;
  localparam CK = 1ns;
  localparam TA = CK * 1 / 4;
  localparam TT = CK * 3 / 4;

  localparam SIM_TIME = 1ms;

  logic clk;
  logic start;
  logic ready = 0;
  logic done  = 0;

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
     .clk_o(clk)
     );

  axi_lite_driver #(.AW(AW), .DW(DW), .TT(TT), .TA(TA)) axi_config_drv = new(axi_config_dv);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(SIW), .UW(UW), .TA(TA), .TT(TT)) axi_slave_drv = new(axi_slave_dv);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(MIW), .UW(UW), .TA(TA), .TT(TT)) axi_master_drv = new(axi_master_dv);

  logic ena[];
  int max_va, l1_va;

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(MIW), .UW(UW)) ax_beat = new;
    automatic axi_test::axi_r_beat  #(.DW(DW), .IW(MIW), .UW(UW)) r_beat = new;

    automatic int idx, ena_save;

    axi_master_drv.reset_master();
    @(posedge ready);

    $display("Checking randomized addresses...");
    while(1) begin
      @(posedge clk);
      void'(randomize(ax_beat) with { ax_beat.ax_addr inside { [0:max_va] } ; });
      ax_beat.ax_user = 'b0; // NOTE: set the user signal to zero for now to prevent other actions
      ax_beat.ax_id   = 'b0; // NOTE: set the id to zero for now to prevent reordering
      ax_beat.ax_size = 3'b101;
      if((ax_beat.ax_addr + 32'h32)/`PAGE_SIZE != ax_beat.ax_addr/`PAGE_SIZE) begin
        // do not allow invalid reads over the page barrier
        continue;
      end
      idx      = ax_beat.ax_addr/`PAGE_SIZE;
      ena_save = ena[idx];
      axi_master_drv.send_ar(ax_beat);
      axi_master_drv.recv_r(r_beat);

      // reject addresses with entries modified during read (FIXME: define this properly)
      if(ena_save != ena[idx]) begin
        continue;
      end

      // check state
      if(ena_save) begin
        if(r_beat.r_resp != 2'b00) begin
          $error("Expected hit at 0x%08x, but got miss instead", ax_beat.ax_addr);
        end else if(r_beat.r_data != 32'hff000000 + ax_beat.ax_addr) begin
          $error("Expected hit from 0x%08x at 0x%08x, but got hit at 0x%08x instead",
                 ax_beat.ax_addr, ax_beat.ax_addr + 32'hff000000, r_beat.r_data);
        end
`ifdef VERBOSE
        $display("Got hit at 0x%08x as expected", ax_beat.ax_addr);
`endif
      end else begin
        if(r_beat.r_resp == 2'b00) begin
          $error("Expected miss at 0x%08x, but got hit instead", ax_beat.ax_addr);
        end
`ifdef VERBOSE
        $display("Got miss at 0x%08x as expected", ax_beat.ax_addr);
`endif
      end
    end
  end

  initial begin
    automatic int address, va, pa, idx;

    localparam integer N_SLICES_ARRAY[`RAB_N_PORTS-1:0] = `N_SLICES_ARRAY;
    localparam integer EN_L2TLB_ARRAY[`RAB_N_PORTS-1:0] = `EN_L2TLB_ARRAY;

    axi_config_drv.reset_master();
    // NOTE: testbench currently assumes N_PORTS == 2 and L2 only on port 1 enabled
    assert(`RAB_N_PORTS == 2 && EN_L2TLB_ARRAY[0] == 0 && EN_L2TLB_ARRAY[1] == 1);
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

    // create dynamic array containing current state of the page
    ena = new[max_va/`PAGE_SIZE];
    for(int i=0; i<ena.size(); ++i) begin
      ena[i] = 1;
    end

    // set master ready to run parallel lookups to invalidations / insertions
    ready = 1;

    $display("Start invaldation/reinsertion process...");
    while(1) begin
      @(posedge clk);
      idx = $urandom_range(0, ena.size()-1);
      if(ena[idx]) begin
        // invalidate this entry
`ifdef VERBOSE
        $display("Invalidating page at 0x%08x", idx*`PAGE_SIZE);
`endif
        axi_config_drv.write_ok(32'h10, idx*`PAGE_SIZE);
        axi_config_drv.write_ok(32'h18, (idx+1)*`PAGE_SIZE-1);
        ena[idx] = 0;
      end else begin
        // reinsert entry
`ifdef VERBOSE
        $display("Reinserting page at 0x%08x", idx*`PAGE_SIZE);
`endif
        va = idx*`PAGE_SIZE;
        pa = 32'hff000000 + va;
        if(idx*`PAGE_SIZE >= l1_va) begin
          address = (N_SLICES_ARRAY[0]+1)*8'h20 + ((va-l1_va)/`PAGE_SIZE)*8'h20;
          axi_config_drv.write_ok(address + 32'h00, va);
          axi_config_drv.write_ok(address + 32'h08, va+`PAGE_SIZE-1);
          axi_config_drv.write_ok(address + 32'h10, pa);
          axi_config_drv.write_ok(address + 32'h18, 3'b111);
          ena[idx] = 1;
        end else begin
          address = 32'h8000 + (idx%`RAB_L2_N_SETS)*4*`RAB_L2_N_SET_ENTRIES + (idx/`RAB_L2_N_SETS)*4;
          axi_config_drv.write_ok(address + 32'h1000, (pa >> 12));
          axi_config_drv.write_ok(address, (va >> 8) | 32'h7);
          ena[idx] = 1;
       end
      end
    end
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

  initial begin
    @(posedge ready);

    #SIM_TIME;

    $display("Success!");
    done =1;
  end

endmodule
