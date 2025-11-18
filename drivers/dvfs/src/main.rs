#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point

use core::convert::Infallible;

use cpufreq::{freq_trait::FreqOps, platforms::xilinx::Xilinx};
use sddf_ipc_types::{MessageWriter, ReadFromMessage};
use sddf_rust::dvfs::dvfs::{DvfsReq, DvfsResp};
use sel4_microkit::{Channel, Handler, MessageInfo, debug_println, protection_domain, with_msg_regs, with_msg_regs_mut};

#[protection_domain]
fn init() -> impl Handler {
    HandlerImpl {}
}

struct HandlerImpl {}

impl Handler for HandlerImpl {
    type Error = Infallible;
    fn protected(
        &mut self,
        channel: Channel,
        msg_info: MessageInfo,
    ) -> Result<MessageInfo, Self::Error> {
        debug_println!("Coming from channel: {}", channel.index());
        
        let message = with_msg_regs(|buf| DvfsReq::read_from_message(msg_info.label(), buf));

        let resp = match message {
            Ok(req) => match req {
                DvfsReq::GetFreq { core_ident } => match Xilinx::get_freq(core_ident) {
                    Ok(freq) => DvfsResp::GetFreq { freq_hz: freq },
                    Err(_) => DvfsResp::Error,
                },
                DvfsReq::SetFreq {
                    core_ident,
                    freq_hz,
                } => match Xilinx::set_freq(core_ident, freq_hz) {
                    Ok(()) => DvfsResp::SetFreq,
                    Err(_) => DvfsResp::Error,
                },
            },
            Err(_) => DvfsResp::Error,
        };

        let (label, count) = with_msg_regs_mut(|buf| resp.write_message(buf)).unwrap();

        debug_println!("exiting from dvfs");

        Ok(MessageInfo::new(label, count))
    }
}
