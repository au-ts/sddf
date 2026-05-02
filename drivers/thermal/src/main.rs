#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point

use core::convert::Infallible;

use microkit_error::MicrokitError::EINVAL;
use sddf_thermal::thermal::{ThermalMessage, ThermalReply};
use sel4_microkit::{protection_domain, Channel, Handler, MessageInfo};
use sel4_microkit_message::MessageInfoExt;
use thermal_protocol::thermal_trait::ThermalHal;
use thermal_rockchip_hal::thermal_rockchip::RK3399ThermalHardware;

const GOVERNOR_CHANNEL_INDEX: usize = 0;
const IRQ_INDEX: usize = 1;
const GOVERNOR_CHANNEL: Channel = sel4_microkit::Channel::new(GOVERNOR_CHANNEL_INDEX);
const IRQ_CHANNEL: Channel = sel4_microkit::Channel::new(IRQ_INDEX);

#[protection_domain]
fn init() -> HandlerImpl {
    let thermal_sensor: RK3399ThermalHardware = unsafe { RK3399ThermalHardware::new() };

    HandlerImpl { thermal_sensor }
}

struct HandlerImpl {
    thermal_sensor: RK3399ThermalHardware,
}

impl Handler for HandlerImpl {
    type Error = Infallible;
    fn notified(&mut self, channel: sel4_microkit::Channel) -> Result<(), Self::Error> {
        if channel != IRQ_CHANNEL {
            core::panic!("unexpected notification from channel {channel:?}")
        }
        // Notify the client that temperature is higher than the threshold
        GOVERNOR_CHANNEL.notify();
        // Acknowledge irqs
        self.thermal_sensor.thermal_ack_irq().unwrap();
        IRQ_CHANNEL.irq_ack().unwrap();
        Ok(())
    }

    fn protected(
        &mut self,
        channel: sel4_microkit::Channel,
        msg_info: sel4_microkit::MessageInfo,
    ) -> Result<sel4_microkit::MessageInfo, Self::Error> {
        if channel != GOVERNOR_CHANNEL {
            core::panic!("unexpected protected procedure call from channel {channel:?} with msg_info={msg_info:?}")
        }
        let msg: ThermalMessage = msg_info.recv::<ThermalMessage>().unwrap();

        let reply: ThermalReply;

        match msg {
            ThermalMessage::GetSensorNum => {
                reply = ThermalReply::SensorNum(
                    self.thermal_sensor
                        .thermal_sensor_get_sensor_number()
                        .unwrap(),
                );
            }
            ThermalMessage::GetTemp(sensor_index) => {
                reply = match self.thermal_sensor.thermal_get_tempareture(sensor_index) {
                    Ok(num) => ThermalReply::Temp(Ok(num)),
                    Err(_) => ThermalReply::Temp(Err(EINVAL)),
                }
            }
            ThermalMessage::SetAlarmTemp(sensor_index, alarm_temp) => {
                reply = match self
                    .thermal_sensor
                    .thermal_set_trip(sensor_index, alarm_temp)
                {
                    Ok(_) => ThermalReply::AlarmTemp(Ok(())),
                    Err(_) => ThermalReply::AlarmTemp(Err(EINVAL)),
                }
            }
        }

        let reply_msg: MessageInfo = MessageInfo::send(reply).unwrap();

        Ok(reply_msg)
    }
}
