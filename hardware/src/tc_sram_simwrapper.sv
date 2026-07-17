// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

module tc_sram_simwrapper #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte
  parameter int unsigned NumPorts     = 32'd2,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "none",   // Simulation initialization
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  parameter              ImplKey      = "none",   // Reference to specific implementation
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
  parameter type         addr_t    = logic [AddrWidth-1:0],
  parameter type         data_t    = logic [DataWidth-1:0],
  parameter type         be_t      = logic [BeWidth-1:0]
) (
  input  logic                 clk_i,      // Clock
  input  logic                 rst_ni,     // Asynchronous reset active low
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o     // read data
);


  tc_sram #(
    .DataWidth(DataWidth  ),
    .NumWords (NumWords   ),
    .NumPorts (NumPorts   ),
    .SimInit  (SimInit    )
  ) i_sram (
    .clk_i  (clk_i        ),
    .rst_ni (rst_ni       ),
    .req_i  (req_i        ),
    .we_i   (we_i         ),
    .addr_i (addr_i       ),
    .wdata_i(wdata_i      ),
    .be_i   (be_i         ),
    .rdata_o(rdata_o      )
  );


/**
 * Memory loader for simulation
 *
 * Include this file in a memory primitive to load a memory array from
 * simulation.
 *
 * Requirements:
 * - A memory array named `sram`.
 * - A parameter `DataWidth` giving the memory width (word size) in bit.
 * - A parameter `NumWords` giving the memory depth in words.
 */

`ifndef SYNTHESIS
  // Task for loading 'sram' with SystemVerilog system task $readmemh()
  export "DPI-C" task simutil_memload;

  task simutil_memload;
    input string file;
    $readmemh(file, i_sram.sram);
  endtask

  // Function for setting a specific element in |sram|
  // Returns 1 (true) for success, 0 (false) for errors.
  export "DPI-C" function simutil_set_mem;

  function int simutil_set_mem(input int index, input bit [1023:0] val);

    // Function will only work for memories <= 1024 bits
    if (DataWidth > 1024) begin
      return 0;
    end

    if (index >= NumWords) begin
      return 0;
    end

    i_sram.sram[index] = val[DataWidth-1:0];
    return 1;
  endfunction

  // Function for getting a specific element in |sram|
  export "DPI-C" function simutil_get_mem;

  function int simutil_get_mem(input int index, output bit [1023:0] val);

    // Function will only work for memories <= 1024 bits
    if (DataWidth > 1024) begin
      return 0;
    end

    if (index >= NumWords) begin
      return 0;
    end

    val = 0;
    val[DataWidth-1:0] = i_sram.sram[index];
    return 1;
  endfunction
`endif

endmodule
