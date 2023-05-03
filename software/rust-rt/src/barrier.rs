use alloc::format;
use core::arch::asm;
use core::sync::atomic::{AtomicU32, Ordering};
use println;

use BARRIER;

pub struct Barrier {
    barrier: AtomicU32,
    num_cores: u32,
}

impl Barrier {
    pub fn new(hartid: u32, num_cores: u32) -> Barrier {
        let b = Barrier {
            barrier: AtomicU32::new(0),
            num_cores: num_cores,
        };
        if hartid == 0 {
            b.barrier.store(0, Ordering::Relaxed);
            println!("barrier initialised");
            mempool_wake_up_all();
            mempool_wfi();
        } else {
            mempool_wfi();
        }
        b
    }

    pub fn wait(&self) {
        if (self.num_cores - 1) == self.barrier.fetch_add(1, Ordering::Relaxed) {
            self.barrier.store(0, Ordering::Relaxed);
            mempool_wake_up_all();
        }
        mempool_wfi();
    }
}

pub fn mempool_wfi() {
    unsafe {
        asm!("wfi");
    }
}

fn mempool_wake_up(hartid: u32) {
    unsafe {
        asm!(
            "la {tmp}, wake_up_reg",        //loading wake_up_reg into a temporary register
            "sw {hartid}, 0({tmp})",        //store hartid into wake_up_reg
            tmp = out(reg) _,
            hartid = in(reg) hartid,
        );
    }
}

//using hartid 0xffffffff wakes up all cores
fn mempool_wake_up_all() {
    mempool_wake_up(u32::MAX);
}

pub fn mempool_barrier_init(hartid: u32) {
    if hartid == 0 {
        BARRIER.store(0, Ordering::Relaxed);
        println!("barrier initialised");
        mempool_wake_up_all();
        mempool_wfi();
    } else {
        mempool_wfi();
    }
}

pub fn mempool_barrier(num_cores: u32) {
    if (num_cores - 1) == BARRIER.fetch_add(1, Ordering::Relaxed) {
        BARRIER.store(0, Ordering::Relaxed);
        mempool_wake_up_all();
    }
    mempool_wfi();
}

pub fn get_core_count() -> u32 {
    let num_cores: u32 = 16;
    // unsafe {
    //     asm!(
    //         "lw {0}, nr_cores_address_reg",
    //         out(reg) num_cores,
    //     );
    // }
    num_cores
}
