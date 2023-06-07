// Copyright 2023 ETH Zurich and 
// University of Bologna

// Solderpad Hardware License
// Version 0.51, see LICENSE for details.

// SPDX-License-Identifier: SHL-0.51

// Author: Chi Zhang <chizhang@iis.ee.ethz.ch>, ETH Zurich
// Date: 07.June.2023

// dram model using dramsys library

import "DPI-C" function void my_lib_call();
import "DPI-C" function int add_dram(input string resources_path, input string simulationJson_path);
import "DPI-C" function int dram_get_inflight_read(input int dram_id);
import "DPI-C" function int dram_can_accept_req(input int dram_id);
import "DPI-C" function int dram_has_rsp(input int dram_id);
import "DPI-C" function void dram_send_req(input int dram_id, input longint addr, input longint length , input longint is_write, inout byte buffer[]);
import "DPI-C" function void dram_get_rsp(input int dram_id, input longint length, inout byte buffer[]);
import "DPI-C" function void dram_load_elf(input int dram_id, input longint dram_base_addr, input string app_path);
import "DPI-C" function void cloes_dram(input int dram_id);


module sim_dram #(
  parameter int unsigned DataWidth      = 32'd512,  // Data signal width
  parameter int unsigned AddrWidth      = 32'd64,    // Addr signal width
  parameter longint unsigned BASE       = 64'h80000000, // DRAM Base addr
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter type         addr_t         = logic [AddrWidth-1:0],
  parameter type         data_t         = logic [DataWidth-1:0]
)(
    input  logic                 clk_i,      // Clock
    input  logic                 rst_ni,     // Asynchronous reset active low
    // requests ports
    input  logic                 req_valid_i,// request valid 
    output logic                 req_ready_o,// request ready
    input  logic                 we_i,       // write enable
    input  addr_t                addr_i,     // request address
    input  data_t                wdata_i,    // write data
    // response ports
    output logic                 rsp_valid_o,
    input  logic                 rsp_ready_i,
    output data_t                rdata_o     // read data
);

typedef logic [7:0] my_byte_t;

int dram_id;

int in_flight_read_dram;
int in_flight_read_this_module;

byte out_buffer[DataWidth/8-1:0];

always_comb begin
    my_byte_t [DataWidth/8-1:0] tmp;
    for (int i = 0; i < (DataWidth/8); i++) begin
        tmp[i] = out_buffer[i];
    end
    rdata_o = tmp;
end

//initialize model (CTRL + DRAM)
initial begin
    string resources_path;
    string simulationJson_path;
    string app_path;
    void'($value$plusargs("DRAMSYS_RES=%s", resources_path));
    void'($value$plusargs("DRAMSYS_CONF=%s", simulationJson_path));
    $display("resources_path= %s\n",resources_path);
    $display("simulationJson_path= %s\n",simulationJson_path);
    if (resources_path.len() == 0 || simulationJson_path.len() == 0) begin
        $fatal(1,"no DRAMsys configuration found!");
    end
    dram_id = add_dram(resources_path, simulationJson_path);
    void'($value$plusargs("app=%s", app_path));
    if (app_path.len() == 0) begin
        $warning("No app found to preload in DRAM !!");
    end else begin
        $display("loading app: %s\n",app_path);
        dram_load_elf(dram_id, BASE, app_path);
    end
end

always_ff @(negedge clk_i or posedge clk_i or negedge rst_ni) begin : proc_dram
    if(~rst_ni) begin
        in_flight_read_this_module <=0;
        in_flight_read_dram <= 0;
        req_ready_o <= 1;
        rsp_valid_o <= 0;

    end else if (clk_i) begin //posedge clk

        if (rsp_valid_o & rsp_ready_i) begin
            rsp_valid_o <= 0;
            in_flight_read_this_module = in_flight_read_this_module -1;
        end

        if (dram_can_accept_req(dram_id)) begin
            req_ready_o <= 1;
        end else begin
            req_ready_o <= 0;
        end

        if (req_valid_i & req_ready_o) begin
            byte in_buffer[DataWidth/8-1:0];
            my_byte_t [DataWidth/8-1:0] tmp;
            tmp = wdata_i;
            for (int i = 0; i < (DataWidth/8); i++) begin
                in_buffer[i] = tmp[i];
            end
            dram_send_req(dram_id, addr_i, DataWidth/8, we_i, in_buffer);
            if (~we_i) begin
                in_flight_read_this_module = in_flight_read_this_module + 1;
            end
        end
        //update inflight read
        in_flight_read_dram = dram_get_inflight_read(dram_id);

    end else begin//negedge clk

        //rsponse 
        if (~rsp_valid_o) begin
            if (dram_has_rsp(dram_id)) begin
                rsp_valid_o <= 1;
                dram_get_rsp(dram_id, DataWidth/8, out_buffer);
            end
        end
            
    end

end



final begin
    cloes_dram(dram_id);
end

endmodule : sim_dram