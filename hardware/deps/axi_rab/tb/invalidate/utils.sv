`ifndef TB_UTILS_SV
`define TB_UTILS_SV

class axi_lite_driver #(
                        parameter int  AW,
                        parameter int  DW,
                        parameter time TA = 0ns,
                        parameter time TT = 0ns
                        ) extends axi_test::axi_lite_driver #(.AW(AW), .DW(DW), .TA(TA), .TT(TT));

  function new(
               virtual AXI_LITE_DV #(
                                     .AXI_ADDR_WIDTH(AW),
                                     .AXI_DATA_WIDTH(DW)
                                     ) axi
               );
    super.new(axi);
  endfunction // new

  task write(input int address_in, input int data_in, output axi_pkg::resp_t resp);
    automatic logic [AW-1:0] address;
    automatic logic [DW-1:0] data;
    automatic logic [DW/8-1:0] strb;
    address = address_in;
    data    = data_in;
    strb    = {DW/8{1'b1}};

    send_aw(address);
    send_w(data, strb);
    recv_b(resp);
  endtask

  task write_ok(input int address_in, input int data_in);
    axi_pkg::resp_t resp;
    write(address_in, data_in, resp);

    if(resp != 'b0) begin
      $error("Expected successful write of %d to 0x%08x, but write failed instead", data_in, address_in);
    end
  endtask // write_ok

  task write_err(input int address_in, input int data_in);
    axi_pkg::resp_t resp;
    write(address_in, data_in, resp);

    if(resp == 'b0) begin
      $error("Expected failed write of %d to 0x%08x, but write succesful instead", data_in, address_in);
    end
  endtask // write_err

  task read_exp(input int address_in, input int data_in);
    automatic logic [AW-1:0] address;
    automatic logic [DW-1:0] data;
    automatic logic [DW/8-1:0] strb;
    axi_pkg::resp_t resp;
    address = address_in;
    strb    = {DW/8{1'b1}};

    send_ar(address);
    recv_r(data, resp);

    if(resp != 'b0) begin
      $error("Expected successful read at 0x%08x, but read failed instead", data, address);
    end else if(data != data_in) begin
      $error("Expected %d at 0x%08x, but got %d instead", data_in, address, data);
    end
  endtask // read_exp

endclass

`endif
