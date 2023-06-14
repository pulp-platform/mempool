// Copyright 2023 ETH Zurich and 
// University of Bologna

// Solderpad Hardware License
// Version 0.51, see LICENSE for details.

// SPDX-License-Identifier: SHL-0.51

// Author: Chi Zhang <chizhang@iis.ee.ethz.ch>, ETH Zurich
// Date: 07.June.2023

// Testbench for dram rtl simulator

module axi_to_dram_tb;

    `include "axi/assign.svh"
    `include "axi/typedef.svh"

    //////////////////////
    //  AXI Parameters  //
    //////////////////////

    localparam int unsigned                 AXI_ADDR_WIDTH              = 32;
    localparam int unsigned                 AXI_DATA_WIDTH              = 512;
    localparam int unsigned                 AXI_STRB_WIDTH              = AXI_DATA_WIDTH / 8;
    localparam int unsigned                 AXI_ID_WIDTH                = 5;
    localparam int unsigned                 AXI_USER_WIDTH              = 5;
    localparam int unsigned                 BASE                        = 32'h8000_0000;

    typedef logic [AXI_ADDR_WIDTH-1:0]      axi_addr_t;
    typedef logic [AXI_DATA_WIDTH-1:0]      axi_data_t;
    typedef logic [AXI_STRB_WIDTH-1:0]      axi_strb_t;
    typedef logic [AXI_ID_WIDTH-1:0]        axi_id_t;
    typedef logic [AXI_USER_WIDTH-1:0]      axi_user_t;

    `AXI_TYPEDEF_ALL(axi, axi_addr_t, axi_id_t, axi_data_t, axi_strb_t, axi_user_t)

    //////////////////////////////////////
    //        Signal Definition         //
    //////////////////////////////////////

    localparam time ClkPeriod = 10ns;
    localparam time ApplTime =  2ns;
    localparam time TestTime =  8ns;

    logic  clk, rst_n;

    axi_req_t                   axi_req;
    axi_resp_t                  axi_resp;

    AXI_BUS_DV #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH  ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) axi_bus_dv(clk);

    `AXI_ASSIGN_TO_REQ(axi_req,axi_bus_dv)
    `AXI_ASSIGN_FROM_RESP(axi_bus_dv, axi_resp)


    //////////////////////////////////////
    //        Clock Generation          //
    //////////////////////////////////////
    initial begin
        rst_n = 0;
        $display("start");
        repeat (3) begin
            #(ClkPeriod/2) clk = 0;
            #(ClkPeriod/2) clk = 1;
        end
        rst_n = 1;
        $display("rst up");
        forever begin
            #(ClkPeriod/2) clk = 0;
            #(ClkPeriod/2) clk = 1;
        end
    end

    //////////////////////
    //        DUT       //
    //////////////////////

    dram_sim_engine #(.ClkPeriodNs(1)) i_dram_sim_engine (.clk_i(clk), .rst_ni(rst_n));

    axi_dram_sim #(
        .AxiAddrWidth(AXI_ADDR_WIDTH),
        .AxiDataWidth(AXI_DATA_WIDTH),
        .AxiIdWidth  (AXI_ID_WIDTH),
        .AxiUserWidth(AXI_USER_WIDTH),
        .BASE        (BASE),
        .axi_req_t   (axi_req_t),
        .axi_resp_t  (axi_resp_t),
        .axi_ar_t    (axi_ar_chan_t),
        .axi_r_t     (axi_r_chan_t),
        .axi_aw_t    (axi_aw_chan_t),
        .axi_w_t     (axi_w_chan_t),
        .axi_b_t     (axi_b_chan_t)
    ) i_axi_dram_sim (
        .clk_i     (clk     ),
        .rst_ni    (rst_n    ),
        .axi_req_i (axi_req ),
        .axi_resp_o(axi_resp)
    );

    //////////////////////////
    //        Driver        //
    //////////////////////////

    typedef axi_test::axi_rand_master #(
        // AXI interface parameters
        .AW ( AXI_ADDR_WIDTH ),
        .DW ( AXI_DATA_WIDTH ),
        .IW ( AXI_ID_WIDTH ),
        .UW ( AXI_USER_WIDTH ),
        .AX_MAX_WAIT_CYCLES(20),
        .AXI_BURST_FIXED(0),
        // Stimuli application and test time
        .TA ( ApplTime ),
        .TT ( TestTime )
    ) axi_master_t;

    axi_master_t axi_master = new(axi_bus_dv);

    //Speed test
    task speedTest(int count);
        automatic axi_master_t::ax_beat_t ar = new ;
        automatic axi_master_t::r_beat_t r = new ;

        ar = axi_master.new_rand_burst(0);
        ar.ax_len = 0;
        ar.ax_size = $clog2(AXI_DATA_WIDTH/8);
        ar.ax_atop = axi_pkg::ATOP_NONE;
        ar.ax_addr = (ar.ax_addr>>$clog2(AXI_DATA_WIDTH/8))<<$clog2(AXI_DATA_WIDTH/8);

        $display("speedTest start!");

        fork
            //send ar
            begin
                for (int i = 0; i < count; i++) begin
                    ar.ax_addr = ar.ax_addr + 64;
                    axi_master.drv.send_ar(ar);
                end
            end
            //receive r
            begin
                for (int i = 0; i < (count*(ar.ax_len+1)); i++) begin
                    axi_master.drv.recv_r(r);
                end
            end
        join

        $display("speedTest done!");
    endtask

    initial begin
        axi_master.reset();
        axi_master.add_memory_region(BASE + 0, BASE + 65636, axi_pkg::NORMAL_NONCACHEABLE_NONBUFFERABLE);
        @(posedge rst_n);
        // axi_master.run(1000,1000);
        speedTest(10000);
        $finish;
    end






endmodule : axi_to_dram_tb
