use alloc::format;
use core::arch::asm;
use core::sync::atomic::{AtomicU32, Ordering};
use println;

use core::convert::TryInto;

use BARRIER;

pub struct Barrier {
    barrier: AtomicU32,
    num_cores: usize,
}

impl Barrier {
    pub fn new(hartid: usize, num_cores: usize) -> Barrier {
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
        if (self.num_cores - 1)
            == self
                .barrier
                .fetch_add(1, Ordering::Relaxed)
                .try_into()
                .unwrap()
        {
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

fn mempool_wake_up(hartid: usize) {
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
    mempool_wake_up(usize::MAX);
}

pub fn mempool_barrier_init(hartid: usize) {
    if hartid == 0 {
        BARRIER.store(0, Ordering::Relaxed);
        println!("barrier initialised");
        mempool_wake_up_all();
        mempool_wfi();
    } else {
        mempool_wfi();
    }
}

pub fn mempool_barrier(num_cores: usize) {
    if (num_cores - 1) == BARRIER.fetch_add(1, Ordering::Relaxed).try_into().unwrap() {
        BARRIER.store(0, Ordering::Relaxed);
        mempool_wake_up_all();
    }
    mempool_wfi();
}

pub fn get_core_count() -> usize {
    let num_cores: usize = 16;
    // unsafe {
    //     asm!(
    //         "lw {0}, nr_cores_address_reg",
    //         out(reg) num_cores,
    //     );
    // }
    num_cores
}
