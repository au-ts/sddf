#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point

use core::convert::Infallible;

use cpufreq::freq_trait::FreqOps;
use sddf_timer::timer::Timer;

use crate::platforms::xilinx::Xilinx;

use sel4_microkit::{debug_println, protection_domain, Handler};

mod platforms;

const TIMER: Timer = Timer::new(sel4_microkit::Channel::new(0));

fn usleep(time_us: u32) {
    let time_ns: u64 = time_us as u64 * 1000;
    for _ in 0..time_ns {
        core::hint::spin_loop(); // Use spin loop hint to reduce contention during the wait
    }
}

#[protection_domain]
fn init() -> impl Handler {
    let res: u64 = Xilinx::get_freq(0);

    debug_println!("Current {:#x}", res);

    let mut past_time: u64 = TIMER.time_now();

    usleep(1000_000);

    let mut current_time: u64 = TIMER.time_now();

    let mut time_elapsed: u64 = current_time - past_time;

    debug_println!("Elapsed time: {} ns", time_elapsed);

    debug_println!("Change clk frequency");

    Xilinx::set_freq(0);

    let res: u64 = Xilinx::get_freq(0);

    debug_println!("Current {:#x}", res);

    past_time = TIMER.time_now();

    usleep(1000_000);

    current_time = TIMER.time_now();

    time_elapsed = current_time - past_time;

    debug_println!("Elapsed time: {} ns", time_elapsed);

    HandlerImpl{}
}

struct HandlerImpl {
}

impl Handler for HandlerImpl
{
    type Error = Infallible;
    
    fn notified(&mut self, channels: sel4_microkit::ChannelSet) -> Result<(), Self::Error> {
        core::panic!(
            "unexpected notification from channels {}",
            channels.display()
        )
    }
    
    fn protected(
        &mut self,
        channel: sel4_microkit::Channel,
        msg_info: sel4_microkit::MessageInfo,
    ) -> Result<sel4_microkit::MessageInfo, Self::Error> {
        core::panic!("unexpected protected procedure call from channel {channel:?} with msg_info={msg_info:?}")
    }
    
    fn fault(
        &mut self,
        child: sel4_microkit::Child,
        msg_info: sel4_microkit::MessageInfo,
    ) -> Result<Option<sel4_microkit::MessageInfo>, Self::Error> {
        core::panic!("unexpected fault from protection domain {child:?} with msg_info={msg_info:?}")
    }
    
    fn take_deferred_action(&mut self) -> Option<sel4_microkit::DeferredAction> {
        None
    }
}