// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "register_interface/typedef.svh"

module axi_uart #(
  parameter type axi_req_t                = logic,
  parameter type axi_resp_t               = logic
) (
  input  logic       clk_i,
  input  logic       rst_ni,
  input  logic       testmode_i,
  // AXI Bus
  input  axi_req_t   axi_req_i,
  output axi_resp_t  axi_resp_o
);

  localparam AddrWidth = $bits(axi_req_i.aw.addr);
  localparam DataWidth = $bits(axi_req_i.w.data);
  localparam StrbWidth = DataWidth/8;

  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [StrbWidth-1:0] strb_t;

  `REG_BUS_TYPEDEF_ALL(uart, addr_t, data_t, strb_t)

  uart_req_t reg_req;
  uart_rsp_t reg_resp;

  axi_to_reg #(
    .ADDR_WIDTH         (AddrWidth               ),
    .DATA_WIDTH         (DataWidth               ),
    .ID_WIDTH           ($bits(axi_req_i.aw.id)  ),
    .USER_WIDTH         ($bits(axi_req_i.aw.user)),
    .AXI_MAX_WRITE_TXNS (1                       ),
    .AXI_MAX_READ_TXNS  (1                       ),
    .DECOUPLE_W         (1'b1                    ),
    .axi_req_t          (axi_req_t               ),
    .axi_rsp_t          (axi_resp_t              ),
    .reg_req_t          (uart_req_t              ),
    .reg_rsp_t          (uart_rsp_t              )
  ) i_axi_to_reg (
    .clk_i      (clk_i     ),
    .rst_ni     (rst_ni    ),
    .testmode_i (testmode_i),
    .axi_req_i  (axi_req_i ),
    .axi_rsp_o  (axi_resp_o),
    .reg_req_o  (reg_req   ),
    .reg_rsp_i  (reg_resp  )
  );

  string str;

  always @(posedge clk_i ) begin
    if (!rst_ni) begin
      str <= "";
    end else begin
      if (reg_req.valid) begin
        if (reg_req.write) begin
          for (int i = 0; i < StrbWidth; i++) begin
            if (reg_req.wstrb[i]) begin
              str <= $sformatf("%s%c", str, reg_req.wdata[i*8+:8]);
            end
          end
          if (reg_req.wdata == 'h0a) begin
            $display("[UART] %s", str);
            str <= "";
          end
        end
      end
    end
  end

  assign reg_resp.rdata = '0;
  assign reg_resp.error = 1'b0;
  assign reg_resp.ready = 1'b1;

endmodule : axi_uart
