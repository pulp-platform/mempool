// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

`include "common_cells/registers.svh"
module simulation_ctrl #(
	parameter type axi_system_req_t = logic,     // AXI request type
  	parameter type axi_system_resp_t = logic    
	)(
	input logic                	clk_i,
	input logic                	rst_ni,

	output axi_system_req_t    	to_mempool_req_o,
  	input  axi_system_resp_t   	to_mempool_resp_i,

  	output logic 				fetch_o
);

	import mempool_pkg::*;

	localparam ctrl_phys_addr = 32'h4000_0000;
    localparam ctrl_size      = 32'h0100_0000;
    localparam l2_phys_addr   = 32'h8000_0000;
    localparam l2_size        = 32'h0700_0000;
    localparam ctrl_virt_addr = ctrl_phys_addr;
    localparam l2_virt_addr   = l2_phys_addr;

    typedef enum logic [2:0] {
        IDLE = '0,
        WAIT_BOOTROM,
        WAKE_UP_AW,
        WAKE_UP_W,
        WAKE_UP_B,
        END} 
    state_t;

    state_t state_q, state_d;
    `FFSRN(state_q, state_d, IDLE, clk_i, rst_ni)

    logic [63:0] boot_cnt_q,boot_cnt_d;
    `FFSRN(boot_cnt_q,boot_cnt_d, '0, clk_i, rst_ni)

    addr_t addr;
    data_t data;

    always_comb begin : proc_sim_ctrl
    	//default
    	to_mempool_req_o.aw.burst = axi_pkg::BURST_INCR;
    	to_mempool_req_o.ar.burst = axi_pkg::BURST_INCR;
    	to_mempool_req_o.aw.cache = axi_pkg::CACHE_MODIFIABLE;
    	to_mempool_req_o.ar.cache = axi_pkg::CACHE_MODIFIABLE;
    	to_mempool_req_o = '{default: '0};
    	fetch_o = 1'b0;
    	state_d = state_q;
    	boot_cnt_d = boot_cnt_q;
    	addr = ctrl_virt_addr + 32'h4;
    	data = {DataWidth{1'b1}};

    	//FSM
    	case (state_q)

    		IDLE: begin
                state_d = WAIT_BOOTROM;
            end

            WAIT_BOOTROM: begin
                if (boot_cnt_q > 1000) begin
                	state_d = WAKE_UP_AW;
                end
                boot_cnt_d = boot_cnt_q + 1;
            end

            WAKE_UP_AW: begin
                to_mempool_req_o.aw.id = 'h18d;
				to_mempool_req_o.aw.addr = ctrl_virt_addr + 32'h4;
				to_mempool_req_o.aw.size = 'h2;
				to_mempool_req_o.aw.burst = axi_pkg::BURST_INCR;
				to_mempool_req_o.aw_valid = 1'b1;
				if (to_mempool_resp_i.aw_ready) begin
					state_d = WAKE_UP_W;
				end
            end

            WAKE_UP_W: begin
				to_mempool_req_o.aw_valid = 1'b0;
				to_mempool_req_o.w.data = data << addr[ByteOffset +: $clog2(AxiDataWidth/DataWidth)] * DataWidth;
				to_mempool_req_o.w.strb = {BeWidth{1'b1}} << addr[ByteOffset +: $clog2(AxiDataWidth/DataWidth)] * BeWidth;
				to_mempool_req_o.w.last = 1'b1;
				to_mempool_req_o.w.user = '0;
				to_mempool_req_o.w_valid = 1'b1;
				if (to_mempool_resp_i.w_ready) begin
					state_d = WAKE_UP_B;
				end
            end

            WAKE_UP_B: begin
				to_mempool_req_o.w_valid = 1'b0;
				to_mempool_req_o.b_ready = 1'b1;
				if (to_mempool_resp_i.b_valid) begin
					assert(to_mempool_resp_i.b.resp == axi_pkg::RESP_OKAY);
					state_d = END;
				end
            end

            END: begin
                
            end
    	
    		default : state_d = END;
    	endcase
    	
    end

endmodule : simulation_ctrl
