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
$display("Testing multiple reads.");

trans_type = "8_BYTE";
addr = 32'h2FF8; // 1 through L2, 3 through L1

CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(0), .transfer_count(4), .transfer_type(trans_type) );

repeat (100) @(posedge ACLK)
Nop;

//-------------------------------------------------------//
$display("Testing multiple writes - bypass YES.");

trans_type = "8_BYTE";
addr = 32'h2FF8; // 1 through L2, 3 through L1

// CLEAR
FILL_LINEAR  (.address_base(addr), .fill_pattern(0),    .cmd_id(2), .transfer_count(4), .transfer_type(trans_type) );
BARRIER_AW();
repeat (100) @(posedge ACLK)
Nop;

// TEST
FILL_LINEAR  (.address_base(addr), .fill_pattern(addr), .cmd_id(0), .transfer_count(4), .transfer_type(trans_type) );
CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(1), .transfer_count(4), .transfer_type(trans_type) );

repeat (100) @(posedge ACLK)
Nop;

//-------------------------------------------------------//
$display("Testing multiple writes - bypass NO.");

trans_type = "256_BYTE";
addr = 32'h2F00; // 1 through L2, 3 through L1

// CLEAR
FILL_LINEAR  (.address_base(addr), .fill_pattern(0),    .cmd_id(2), .transfer_count(4), .transfer_type(trans_type) );
BARRIER_AW();
repeat (100) @(posedge ACLK)
Nop;

// TEST
FILL_LINEAR  (.address_base(addr), .fill_pattern(addr), .cmd_id(0), .transfer_count(4), .transfer_type(trans_type) );
CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(1), .transfer_count(4), .transfer_type(trans_type) );

repeat (100) @(posedge ACLK)
Nop;

//-------------------------------------------------------//
$display("L2 DMA & L1 PTW.");

addr   = 32'h2000; // DMA through L2
addr_2 = 32'h3000; // PTW through L1

// Here we use READ_LINEAR as the CHECK_LINEAR task only finishes after getting the response.
READ_LINEAR  (.address_base(addr_2), .cmd_id(01), .transfer_count(1), .transfer_type("8_BYTE") );
READ_LINEAR  (.address_base(addr_2), .cmd_id(02), .transfer_count(1), .transfer_type("8_BYTE") );

READ_LINEAR  (.address_base(addr          ), .cmd_id(11), .transfer_count(1), .transfer_type("64_BYTE") );
READ_LINEAR  (.address_base(addr + 32'h40 ), .cmd_id(12), .transfer_count(1), .transfer_type("64_BYTE") );

READ_LINEAR  (.address_base(addr_2), .cmd_id(03), .transfer_count(1), .transfer_type("8_BYTE") );

READ_LINEAR  (.address_base(addr          ), .cmd_id(13), .transfer_count(1), .transfer_type("24_BYTE") );
READ_LINEAR  (.address_base(addr + 32'h18 ), .cmd_id(14), .transfer_count(1), .transfer_type("64_BYTE") );

READ_LINEAR  (.address_base(addr_2), .cmd_id(04), .transfer_count(1), .transfer_type("8_BYTE") );

BARRIER_AR();

repeat (100) @(posedge ACLK)
Nop;

//-------------------------------------------------------//
$display("L2 & L2 Reconfiguration.");

// Sync with test.sv (drives the config port).
READ_LINEAR  (.address_base(32'hF000), .cmd_id(0), .transfer_count(1), .transfer_type("8_BYTE") );
BARRIER_AR();

addr   = 32'h22000; // DMA through L2
CHECK_LINEAR (.address_base(addr), .check_pattern(addr), .cmd_id(1), .transfer_count(4), .transfer_type("64_BYTE") );

BARRIER_AR();

repeat (100) @(posedge ACLK)
Nop;

//-------------------------------------------------------//
$display("Custom Tests.");

trans_type = "16_BYTE";
addr = 32'h31D4; // through L1

READ_LINEAR  (.address_base(addr), .cmd_id(1), .transfer_count(4), .transfer_type(trans_type) );

BARRIER_AR();

trans_type = "24_BYTE";
FILL_LINEAR  (.address_base(addr), .fill_pattern(addr), .cmd_id(0), .transfer_count(1), .transfer_type(trans_type) );

eoc = 1'b1;
