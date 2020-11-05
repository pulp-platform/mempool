// Test Linear Fill


Nop;

//TEST STORE_LOAD 8BYTE
BASE_ADDRESS = 32'h0000_0000;
FILL_LINEAR ( .address_base(BASE_ADDRESS),   .fill_pattern(32'hC1A00000), .transfer_count(COUNT_8B), .transfer_type("8_BYTE") );
BARRIER_AW();
CHECK_LINEAR  ( .address_base(BASE_ADDRESS), .check_pattern(32'hC1A00000), .transfer_count(COUNT_8B), .transfer_type("8_BYTE") );
BARRIER_AR();
Nop;


//TEST STORE_LOAD 16BYTE
Nop;
BASE_ADDRESS = 32'h0000_0000;
FILL_LINEAR ( .address_base(BASE_ADDRESS),   .fill_pattern(32'hBAFE0000), .transfer_count(COUNT_16B), .transfer_type("16_BYTE") );
BARRIER_AW();
CHECK_LINEAR  ( .address_base(BASE_ADDRESS), .check_pattern(32'hBAFE0000), .transfer_count(COUNT_16B), .transfer_type("16_BYTE") );
BARRIER_AR();
Nop;

//TEST STORE_LOAD 32BYTE
BASE_ADDRESS = 32'h0000_0000;
FILL_LINEAR ( .address_base(BASE_ADDRESS),   .fill_pattern(32'hE1A00000), .transfer_count(COUNT_32B), .transfer_type("32_BYTE") );
BARRIER_AW();
CHECK_LINEAR  ( .address_base(BASE_ADDRESS), .check_pattern(32'hE1A00000), .transfer_count(COUNT_32B), .transfer_type("32_BYTE") );
BARRIER_AR();
Nop;


BASE_ADDRESS = 32'h0000_0000;
FILL_RANDOM  ( .address_base(BASE_ADDRESS),   .fill_pattern(32'h00F10000), .transfer_count(COUNT_32B), .transfer_type("32_BYTE") ); 
BARRIER_AW();