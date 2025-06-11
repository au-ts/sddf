#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point

use core::convert::Infallible;

use sel4_microkit::{debug_println, protection_domain, Handler, MessageInfo};
use sel4_microkit_message::{
    types::{MessageRecv, MessageSend},
    MessageInfoExt,
};

const THERMAL_SENSOR: sel4_microkit::Channel = sel4_microkit::Channel::new(0);

#[derive(serde::Serialize, serde::Deserialize)]
pub enum ThermalMessage {
    GetSensorNum,
    GetTemp(u32),
    SetAlarmTemp(u32, u32),
}

#[derive(serde::Serialize, serde::Deserialize)]
pub enum ThermalReply {
    SensorNum(u32),
    GetTemp(u32),
    SetAlarmTemp,
}

#[derive(Debug)]
pub enum SimpleError {
    Success = 0,
    Error = 1,
}

impl MessageSend for ThermalMessage {
    type Label = u64;

    type Error = SimpleError;

    fn write_message(self, buf: &mut [u8]) -> Result<(Self::Label, usize), Self::Error> {
        let len: usize =
            bincode::serde::encode_into_slice(self, buf, bincode::config::standard()).unwrap();
        Ok((0, len))
    }
}

impl MessageRecv for ThermalReply {
    type Label = u64;

    type Error = SimpleError;

    fn read_message(label: Self::Label, buf: &[u8]) -> Result<Self, Self::Error> {
        let (res, len) =
            bincode::serde::decode_from_slice::<ThermalReply, _>(buf, bincode::config::standard()).unwrap();
        Ok(res)
    }
}

pub fn thermal_sensor_get_temperature(channel: sel4_microkit::Channel, sensor_channel: u32) -> u32 {
    let meg: MessageInfo = MessageInfo::send(ThermalMessage::GetTemp(sensor_channel)).unwrap();

    let reply = channel.pp_call(meg);
    0
}

pub fn thermal_sensor_get_sensor_num(channel: sel4_microkit::Channel) -> MessageInfo {
    let meg: MessageInfo = MessageInfo::send(ThermalMessage::GetSensorNum).unwrap();

    channel.pp_call(meg)
}

pub fn thermal_sensor_set_alarm_temp(
    channel: sel4_microkit::Channel,
    sensor_channel: u32,
    alarm_temp: u32,
) -> MessageInfo {
    let meg: MessageInfo =
        MessageInfo::send(ThermalMessage::SetAlarmTemp(sensor_channel, alarm_temp)).unwrap();

    channel.pp_call(meg)
}

#[protection_domain]
fn init() -> HandlerImpl {
    HandlerImpl {}
}

struct HandlerImpl {}

impl Handler for HandlerImpl {
    type Error = Infallible;
    fn notified(&mut self, channel: sel4_microkit::Channel) -> Result<(), Self::Error> {
        if channel == THERMAL_SENSOR {
        } else {
            debug_println!("unexpected notification from channel {channel:?}");
        }
        Ok(())
    }
}
