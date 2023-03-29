/*
Based on https://github.com/noahzarro/pulp-print
*/

use core::arch::asm;

pub use numtoa;

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
    ( $($arg:tt ),*) => {{
        $(
            println::printf($arg);
            println::printf(" ");
        )*
        println::end_line();
    }};

}

#[macro_export]
macro_rules! print {
    ( $( $arg:tt ), *) => {{
        $(
            println::printf($arg);
            println::printf(" ");
        )*
    }};
}

pub enum Format {
    Dec,
    Hex,
    Bin,
}

#[macro_export]
macro_rules! print_nr {
    ($name:tt,$number:tt,$format:path) => {{
        use println::numtoa::NumToA;
        use println::printf;
        printf($name);
        printf(": ");
        let mut buf = [0u8; 100];
        let number = match $format {
            Format::Hex => $number.numtoa_str(16, &mut buf),
            Format::Bin => $number.numtoa_str(2, &mut buf),
            _ => $number.numtoa_str(10, &mut buf),
        };

        match $format {
            Format::Hex => printf("0x"),
            Format::Bin => printf("0b"),
            _ => (),
        };
        printf(number);
        printf("\n");
    }};
}

#[macro_export]
macro_rules! print_nr_only {
    ($number:tt,$format:path) => {{
        use println::numtoa::NumToA;
        use println::printf;
        let mut buf = [0u8; 100];
        let number = match $format {
            Format::Hex => $number.numtoa_str(16, &mut buf),
            Format::Bin => $number.numtoa_str(2, &mut buf),
            _ => $number.numtoa_str(10, &mut buf),
        };
        printf(number);
        printf("\n");
    }};
}
