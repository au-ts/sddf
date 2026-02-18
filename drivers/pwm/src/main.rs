#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point

use core::convert::Infallible;

use pwm_protocol::pwm_fan::Fan;
use pwm_rockchip_hal::pwm_rockchip::RockchipPwmHardware;
use sddf_pwm::pwm::PwmMessage;
use sel4_microkit::{protection_domain, Channel, Handler, MessageInfo};
use sel4_microkit_message::MessageInfoExt;

const GOVERNOR_CHANNEL_INDEX: usize = 0;
const GOVERNOR_CHANNEL: Channel = sel4_microkit::Channel::new(GOVERNOR_CHANNEL_INDEX);

const FAN_PWM_ADDR: u32 = 0xff420010;

#[protection_domain]
fn init() -> HandlerImpl {
    let pwm: RockchipPwmHardware = unsafe { RockchipPwmHardware::new(FAN_PWM_ADDR) };

    let fan: Fan<RockchipPwmHardware> = Fan::new(pwm);

    HandlerImpl { fan }
}

struct HandlerImpl {
    fan: Fan<RockchipPwmHardware>,
}

impl Handler for HandlerImpl {
    type Error = Infallible;

    fn protected(
        &mut self,
        channel: sel4_microkit::Channel,
        msg_info: sel4_microkit::MessageInfo,
    ) -> Result<sel4_microkit::MessageInfo, Self::Error> {
        if channel != GOVERNOR_CHANNEL {
            core::panic!("unexpected protected procedure call from channel {channel:?} with msg_info={msg_info:?}")
        }
        let msg: PwmMessage = msg_info.recv::<PwmMessage>().unwrap();
        match msg {
            PwmMessage::ConfigFanSpeed(fan_speed) => {
                match fan_speed {
                    sddf_pwm::pwm::FanSpeed::Stopped => self.fan.config_fan_speed(pwm_protocol::pwm_fan::FanSpeed::Stopped),
                    sddf_pwm::pwm::FanSpeed::Low => self.fan.config_fan_speed(pwm_protocol::pwm_fan::FanSpeed::Low),
                    sddf_pwm::pwm::FanSpeed::Medium => self.fan.config_fan_speed(pwm_protocol::pwm_fan::FanSpeed::Medium),
                    sddf_pwm::pwm::FanSpeed::High => self.fan.config_fan_speed(pwm_protocol::pwm_fan::FanSpeed::High),
                    sddf_pwm::pwm::FanSpeed::Full => self.fan.config_fan_speed(pwm_protocol::pwm_fan::FanSpeed::Full),
                }
            },
        }.unwrap();
        Ok(MessageInfo::new(0, 0))
    }
}