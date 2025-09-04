module transactions_table
  import cf_math_pkg::idx_width;
#(
  parameter int NumPorts         = 4,
  parameter int NumTransactions  = 8,
  parameter int unsigned TransactionsWidth = idx_width(NumTransactions),
  parameter type resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  // request port
  input   resp_t [NumPorts-1:0]   resp_payload_i,
  input   logic  [NumPorts-1:0]   resp_valid_i,
  output  logic  [NumPorts-1:0]   resp_ready_o,
  // response port
  output  resp_t [NumPorts-1:0]  resp_payload_o,
  output  logic  [NumPorts-1:0]  resp_valid_o,
  input   logic  [NumPorts-1:0]  resp_ready_i
);

  // Table for storing per-transaction data
  resp_t [NumTransactions-1:0][NumPorts-1:0] table_data_q;
  logic  [NumTransactions-1:0][NumPorts-1:0] table_valid_q;

  // Flag indicating when all ports of a transaction are valid
  logic  [NumTransactions-1:0] table_allvalid;
  logic  [TransactionsWidth-1:0] selected;

  // Sequential update of table_data and valid bits
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      table_data_q  <= '0;
      table_valid_q <= '0;
    end else begin
      // Capture incoming data
      for (int p=0; p<NumPorts; p++) begin
        if (resp_valid_i[p] && resp_ready_o[p]) begin
          table_data_q[resp_payload_i[p].id][p]  <= resp_payload_i[p];
          table_valid_q[resp_payload_i[p].id][p] <= 1'b1;
        end
      end

      // Clear entries when transaction is consumed
      for (int t=0; t<NumTransactions; t++) begin
        if (table_allvalid[t] && (&resp_ready_i) && (selected == t)) begin
          table_valid_q[t] <= '0;
        end
      end
    end
  end

  // Compute allvalid per transaction
  for(genvar t=0; t<NumTransactions; t++) begin
    assign table_allvalid[t] = &table_valid_q[t];
  end

  // Simple: pick the first completed transaction to output
  assign resp_payload_o = table_data_q[selected];
  assign resp_valid_o = {NumPorts{table_allvalid[selected]}};
  always_comb begin
    selected = '0;
    for (int t=0; t<NumTransactions; t++) begin
      if (table_allvalid[t]) begin
        selected = t;
      end
    end
  end

  // ready_o: we can accept input whenever that entry has not yet been set
  for (genvar p=0; p<NumPorts; p++) begin
    assign resp_ready_o[p] = 1'b1; //~table_valid_q[resp_payload_i[p].id][p]; // resp_ready_i[p];
  end



endmodule
