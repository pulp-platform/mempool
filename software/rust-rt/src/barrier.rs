use  core::arch::asm;
use core::sync::atomic::Ordering;
use println;
use alloc::format;

use BARRIER;

pub fn mempool_wfi(){
    unsafe{
        asm!("wfi");
    }
}

fn mempool_wake_up(hartid: u32){
    unsafe{
        asm!(
            "la {tmp}, wake_up_reg",
            "sw {hartid}, 0({tmp})",
            tmp = out(reg) _,
            hartid = in(reg) hartid,
        );
    }
}

fn mempool_wake_up_all(){
    mempool_wake_up(u32::MAX);
}

pub fn mempool_barrier_init(hartid: u32){
    if hartid == 0 {
        BARRIER.store(0, Ordering::Relaxed);
        println!("barrier initialised");
        mempool_wake_up_all();
        mempool_wfi();
    }
    else{
        mempool_wfi();
    }
}

pub fn mempool_barrier(num_cores: u32){
    if (num_cores - 1) == BARRIER.fetch_add(1, Ordering::Relaxed){
        BARRIER.store(0, Ordering::Relaxed);
        mempool_wake_up_all();
    }
    mempool_wfi();
}
