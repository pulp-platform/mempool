/*
Based on https://github.com/noahzarro/pulp-print
*/

use core::arch::asm;

pub fn printf(text: &str) {
    for byte in text.as_bytes() {
        unsafe {
            asm!(
                "la t1, fake_uart",
                "sb	{0}, 0(t1)",
                in(reg) *byte as u8,
            );
        };
    }
}

pub fn end_line() {
    unsafe {
        asm!(
            "la t1, fake_uart", //get adress of fake_uart register
            "li t0, 0x0A",      //load 0x0A (ASCII '\n')
            "sb t0, 0(t1)",     //store it to fake_uart
        );
    }
}

#[macro_export]
macro_rules! println {
    ( $($arg:tt),*) => {{
        println::printf(format!($($arg),*).as_str());
        println::end_line();
    }};

}

#[macro_export]
macro_rules! print {
    ( $( $arg:tt ), *) => {{
        println::printf(format!($($arg),*).as_str());
    }};
}
