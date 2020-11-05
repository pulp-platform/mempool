int type_num;
int addr;
int addr_2;
int data;
string trans_type;

Nop;

//-------------------------------------------------------//
$display("Initialize memory.");

trans_type = "256_BYTE";
addr = 32'h10001000;
data = 32'h1000;
FILL_LINEAR  (.address_base(addr), .fill_pattern(data), .cmd_id(0), .transfer_count(512), .transfer_type(trans_type) );

CHECK_LINEAR (.address_base(addr), .check_pattern(data), .cmd_id(1), .transfer_count(512), .transfer_type(trans_type) );

BARRIER_AR();
BARRIER_AW();

repeat (100) @(posedge ACLK)
Nop;

//-------------------------------------------------------//
$display("Testing multi hit.");

trans_type = "8_BYTE";

$display("L1");
addr = 32'h0010;
CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(0), .transfer_count(1), .transfer_type(trans_type) );

$display("L2");
addr = 32'h0100;
CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(0), .transfer_count(1), .transfer_type(trans_type) );
addr = 32'h1000;
CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(0), .transfer_count(1), .transfer_type(trans_type) );
addr = 32'h2000;
CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(0), .transfer_count(1), .transfer_type(trans_type) );

repeat (100) @(posedge ACLK)
Nop;


eoc = 1'b1;
