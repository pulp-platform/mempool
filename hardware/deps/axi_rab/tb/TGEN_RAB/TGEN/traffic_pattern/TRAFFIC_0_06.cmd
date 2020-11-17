


// int type_num;
// int addr;
// int data;
// string trans_type;
// int seed;
//
// seed = 920;
// $display(" Seed for Random Number generator is %d",seed);
// void'($urandom(seed));
//
// Nop;
// for (int i=0; i<1024; i++) begin
//   //srandom(546);
//   type_num = $urandom_range(4,0);
//   if(type_num==0) trans_type = "8_BYTE";
// 	if(type_num==1) trans_type = "16_BYTE";
// 	if(type_num==2) trans_type = "32_BYTE";
// 	if(type_num==3) trans_type = "64_BYTE";
// 	if(type_num==4) trans_type = "256_BYTE";
// //  data = $urandom_range(100,0);
//   addr = $urandom_range(1024*4*16,0);
//   addr = addr/4;
//   addr = addr*4;
//   $display("Sending AXI: addr=%h, type=%s",addr,trans_type);
//   FILL_LINEAR ( .address_base(addr),   .fill_pattern(addr), .transfer_count(COUNT_ONE), .transfer_type(trans_type) );
// end

FILL_LINEAR ( .address_base(32'h00001000),   .fill_pattern(32'h00001000), .transfer_count(COUNT_ONE), .transfer_type("4_BYTE") );

FILL_LINEAR ( .address_base(32'h00000100),   .fill_pattern(32'h00000100), .transfer_count(COUNT_ONE), .transfer_type("256_BYTE") );
//repeat (50) @(posedge ACLK);
FILL_LINEAR ( .address_base(32'h00001010),   .fill_pattern(32'h00001010), .transfer_count(COUNT_ONE), .transfer_type("4_BYTE") );

FILL_LINEAR ( .address_base(32'h00001020),   .fill_pattern(32'h00001020), .transfer_count(COUNT_ONE), .transfer_type("4_BYTE") );

FILL_LINEAR ( .address_base(32'h00001030),   .fill_pattern(32'h00001030), .transfer_count(COUNT_ONE), .transfer_type("4_BYTE") );

FILL_LINEAR ( .address_base(32'h00001040),   .fill_pattern(32'h00001040), .transfer_count(COUNT_ONE), .transfer_type("4_BYTE") );
