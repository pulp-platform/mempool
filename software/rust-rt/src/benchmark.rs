use core::arch::asm;

pub fn start_benchmark() {
    unsafe {
        asm!(
            "csrw 0x7d0, 1", // 0x7d0 is trace reg
            options(nomem)   // memory barrier
        );
    }
}

pub fn stop_benchmark() {
    unsafe {
        asm!(
            "csrw 0x7d0, 0", // 0x7d0 is trace reg
            options(nomem)   // memory barrier
        );
    }
}
