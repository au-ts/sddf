#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point

use core::convert::Infallible;

use cpufreq::freq_trait::FreqOps;

use crate::platforms::xilinx::Xilinx;

use sel4_microkit::{debug_println, protection_domain, Handler};

mod platforms;

mod helper;

#[protection_domain]
fn init() -> impl Handler {
    unsafe {
        helper::counter_init();
    }

    let res: u64 = Xilinx::get_freq(0);

    debug_println!("Current {:#x}", res);

    unsafe {
        let pre_count = helper::read_count();
        helper::wait();
        let post_count = helper::read_count();
        helper::print_count(post_count - pre_count);
    }

    debug_println!("Change clk frequency");

    Xilinx::set_freq(0);

    let res: u64 = Xilinx::get_freq(0);

    debug_println!("Current {:#x}", res);

    unsafe {
        let pre_count = helper::read_count();
        helper::wait();
        let post_count = helper::read_count();
        helper::print_count(post_count - pre_count);
    }

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