/// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
/// Demux based on address
module snitch_addr_demux #(
    parameter int unsigned NrOutput            = 2    ,
    parameter int unsigned AddressWidth        = 32   ,
    parameter int unsigned NumRules            = 1    , // Routing rules
    parameter int unsigned MaxOutStandingReads = 2    ,
    parameter type req_t                       = logic,
    parameter type resp_t                      = logic,
    /// Dependent parameters, DO NOT OVERRIDE!
    localparam integer LogNrOutput             = $clog2(NrOutput)
  ) (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    // request port
    input  logic [AddressWidth-1:0] req_addr_i,
    input  logic                    req_write_i,
    input  req_t                    req_payload_i,
    input  logic                    req_valid_i,
    output logic                    req_ready_o,

    output resp_t                resp_payload_o,
    output logic                 resp_valid_o,
    input  logic                 resp_ready_i,
    // response port
    output req_t  [NrOutput-1:0] req_payload_o,
    output logic  [NrOutput-1:0] req_valid_o,
    input  logic  [NrOutput-1:0] req_ready_i,

    input  resp_t [NrOutput-1:0] resp_payload_i,
    input  logic  [NrOutput-1:0] resp_valid_i,
    output logic  [NrOutput-1:0] resp_ready_o,

    input mempool_pkg::address_map_t [NumRules-1:0] address_map_i
  );

  logic [NrOutput-1:0] fwd;
  logic                id_full, id_empty;
  logic                req_ready, req_valid;
  logic                push_id_fifo, pop_id_fifo;


  logic [LogNrOutput-1:0]      slave_select;
  logic [NumRules-1:0]         addr_match;
  logic [$clog2(NumRules)-1:0] rule_select;

  assign slave_select = address_map_i[rule_select].slave_idx;

  // Address Decoder
  always_comb begin : addr_decoder
    for (int i = 0; i < NumRules; i++) begin
      addr_match[i] = (req_addr_i & address_map_i[i].mask) == address_map_i[i].value;
    end
  end

  find_first_one #(
    .WIDTH(NumRules)
  ) find_slave_select (
    .in_i       ( addr_match   ),
    .first_one_o( rule_select  ),
    .no_ones_o  ( /* Unused */ )
  );

  stream_demux #(
    .N_OUP ( NrOutput )
  ) i_stream_demux (
    .inp_valid_i ( req_valid    ),
    .inp_ready_o ( req_ready    ),
    .oup_sel_i   ( slave_select ),
    .oup_valid_o ( req_valid_o  ),
    .oup_ready_i ( req_ready_i  )
  );

  // we need space in the return id fifo for reads, silence if no space is available
  assign req_valid   = (~id_full | req_write_i) & req_valid_i;
  assign req_ready_o = (~id_full | req_write_i) & req_ready  ;

  for (genvar i = 0; i < NrOutput; i++) begin : gen_req_outputs
    assign req_payload_o[i] = req_payload_i;
  end

  assign push_id_fifo = req_valid & req_ready_o & ~req_write_i ;
  assign pop_id_fifo  = resp_valid_o & resp_ready_i;
  // Remember IDs for correct forwarding of read data
  fifo_v3 #(
    .DATA_WIDTH ( NrOutput            ),
    .DEPTH      ( MaxOutStandingReads )
  ) i_id_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0                        ),
    .testmode_i ( 1'b0                        ),
    .full_o     ( id_full                     ),
    .empty_o    ( id_empty                    ),
    .usage_o    (                             ),
    .data_i     ( (req_valid_o & req_ready_i) ),
    .push_i     ( push_id_fifo                ),
    .data_o     ( fwd                         ),
    .pop_i      ( pop_id_fifo                 )
  );

  always_comb begin
    resp_payload_o = '0;
    resp_valid_o   = '0;
    for (int i = 0; i < NrOutput; i++) begin
      if (fwd[i]) begin
        resp_payload_o = resp_payload_i[i];
        resp_valid_o   = resp_valid_i[i]  ;
      end
    end
  end

  for (genvar i = 0; i < NrOutput; i++) begin : gen_resp_ready
    assign resp_ready_o[i] = fwd[i] ? resp_ready_i : 1'b0;
  end

  /* pragma translate_off */
  `ifdef FORMAL
  logic f_past_valid;
  initial f_past_valid = 1'b0;
  always @(posedge clk_i)
    f_past_valid <= 1'b1;
  // assert reset in time step zero and deassert
  assume property (@(posedge clk_i) !f_past_valid |-> !rst_ni);
  // make sure that we get a response for each read we issued
  for (genvar i = 0; i < NrOutput; i++) begin
    assume property (@(posedge clk_i) disable iff (!rst_ni) (resp_valid_i[i] & resp_ready_o[i]) |-> $past(req_valid_o[i] & req_ready_i[i] & !req_write_i));
  end
  `endif
  // check that we propagate a downstream request directly (e.g. combinatorial)
  assert property (@(posedge clk_i) disable iff (!rst_ni) (req_valid_i & req_ready_o) |-> |(req_valid_o & req_ready_i));
  // check that we are not overflowing the fifo
  assert property (@(posedge clk_i) disable iff (!rst_ni) push_id_fifo |-> !id_full);
  // check that we are not allocating a slot in the id fifo for writes
  assert property (@(posedge clk_i) disable iff (!rst_ni) push_id_fifo |-> !req_write_i);
  // check that we never underflow the fifo
  assert property (@(posedge clk_i) disable iff (!rst_ni) pop_id_fifo |-> !id_empty);
/* pragma translate_on */

endmodule
