


int type_num;
int addr;
int data;
string trans_type;
int seed;
int rw_type;
seed = 479;
$display(" Seed for Random Number generator is %d",seed);
void'($urandom(seed));
repeat (8000) @(posedge ACLK)
Nop;
for (int i=0; i<2048*2; i++) begin
  rw_type = $urandom_range(1,0);
//  rw_type = 1;
  type_num = $urandom_range(4,0);
//  type_num = type_num * rw_type;
  if(type_num==0) trans_type = "8_BYTE";
	if(type_num==1) trans_type = "16_BYTE";
	if(type_num==2) trans_type = "32_BYTE";
	if(type_num==3) trans_type = "64_BYTE";
	if(type_num==4) trans_type = "256_BYTE";
//  data = $urandom_range(100,0);
  addr = $urandom_range(1024*4*40,0);
  addr = addr/8;
  addr = addr*8;
  if(type_num==4) addr = addr & 32'hffffff00;
  if(type_num==3) addr = addr & 32'hffffff00;
	if(type_num==2) addr = addr & 32'hffffffe0;
  if(type_num==1) addr = addr & 32'hfffffff0;

  if (rw_type == 1) begin
     $display("Sending AXI Write: addr=%h, type=%s",addr,trans_type);
     FILL_LINEAR ( .address_base(addr),   .fill_pattern(addr), .cmd_id(i), .transfer_count(COUNT_ONE), .transfer_type(trans_type) );
  end
  if (rw_type == 0) begin
     if (trans_type == "256_BYTE" || trans_type == "64_BYTE") trans_type = "32_BYTE";
     $display("Sending AXI Read: addr=%h, type=%s",addr,trans_type);
     CHECK_LINEAR (.address_base(addr),  .check_pattern(addr), .cmd_id(i), .transfer_count(COUNT_ONE), .transfer_type(trans_type) );
  end
@(posedge ACLK);
@(posedge ACLK);
@(posedge ACLK);


end
