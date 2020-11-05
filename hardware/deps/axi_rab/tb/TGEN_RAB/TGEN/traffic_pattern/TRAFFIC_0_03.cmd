// Test Linear Fill

//TEST STORE_LOAD 4BYTE
Nop;
BASE_ADDRESS = 32'h0000_0000;
FILL_LINEAR ( .address_base(BASE_ADDRESS+COUNT_4B*4*SRC_ID),   .fill_pattern(32'hA0C00000), .transfer_count(COUNT_4B), .transfer_type("4_BYTE") );
BARRIER_AW();
CHECK_LINEAR  ( .address_base(BASE_ADDRESS+COUNT_4B*4*SRC_ID), .check_pattern(32'hA0C00000), .transfer_count(COUNT_4B), .transfer_type("4_BYTE") );
BARRIER_AR();
Nop;

//TEST STORE_LOAD 4BYTE
BASE_ADDRESS = 32'h0000_0000;
FILL_LINEAR ( .address_base(BASE_ADDRESS+COUNT_8B*8*SRC_ID),   .fill_pattern(32'hA0C10000), .transfer_count(COUNT_8B), .transfer_type("8_BYTE") );
BARRIER_AW();
CHECK_LINEAR  ( .address_base(BASE_ADDRESS+COUNT_8B*8*SRC_ID), .check_pattern(32'hA0C10000), .transfer_count(COUNT_8B), .transfer_type("8_BYTE") );
BARRIER_AR();
Nop;


//TEST STORE_LOAD 16BYTE
Nop;
BASE_ADDRESS = 32'h0000_0000;
FILL_LINEAR ( .address_base(BASE_ADDRESS+COUNT_16B*16*SRC_ID),   .fill_pattern(32'hA0C20000), .transfer_count(COUNT_16B), .transfer_type("16_BYTE") );
BARRIER_AW();
CHECK_LINEAR  ( .address_base(BASE_ADDRESS+COUNT_16B*16*SRC_ID), .check_pattern(32'hB0C20000), .transfer_count(COUNT_16B), .transfer_type("16_BYTE") );
BARRIER_AR();
Nop;

//TEST STORE_LOAD 16BYTE
BASE_ADDRESS = 32'h0000_0000;
FILL_LINEAR ( .address_base(BASE_ADDRESS+COUNT_32B*32*SRC_ID),   .fill_pattern(32'hA0C30000), .transfer_count(COUNT_32B), .transfer_type("32_BYTE") );
BARRIER_AW();
CHECK_LINEAR  ( .address_base(BASE_ADDRESS+COUNT_32B*32*SRC_ID), .check_pattern(32'hA0C30000), .transfer_count(COUNT_32B), .transfer_type("32_BYTE") );
BARRIER_AR();
Nop;

BASE_ADDRESS = 32'h0005_0000;

FILL_LINEAR ( .address_base(32'h0005_0000),   .fill_pattern(32'hABBA0000), .transfer_count(1), .transfer_type("4_BYTE") );
FILL_LINEAR ( .address_base(32'h0005_0004),   .fill_pattern(32'hABBA0000), .transfer_count(1), .transfer_type("4_BYTE") );
FILL_LINEAR ( .address_base(32'h0005_0008),   .fill_pattern(32'hABBA0000), .transfer_count(1), .transfer_type("4_BYTE") );
FILL_LINEAR ( .address_base(32'h0005_000C),   .fill_pattern(32'hABBA0000), .transfer_count(1), .transfer_type("4_BYTE") );


//FILL_RANDOM   ( .address_base(BASE_ADDRESS),   .fill_pattern(32'h03F10000), .transfer_count(COUNT_32B), .transfer_type("32_BYTE") ); 

BARRIER_AW();