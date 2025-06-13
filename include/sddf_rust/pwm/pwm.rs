use microkit_error::MicrokitError;
use sel4_microkit::MessageInfo;
use sel4_microkit_message::{
    types::{MessageRecv, MessageSend},
    MessageInfoExt,
};

/// Represents predefined fan speed levels.
///
/// This enum maps human-readable speed settings to the underlying `u8` value
/// that will be used to control the PWM duty cycle. The values range from 0 (stopped)
/// to 255 (full speed).
#[repr(u8)]
#[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq)]
pub enum FanSpeed {
    Stopped = 0,  // 0%   (0/255)
    Low = 64,     // ~25% (64/255)
    Medium = 128, // ~50% (128/255)
    High = 192,   // ~75% (192/255)
    Full = 255,   // 100% (255/255)
}

#[derive(serde::Serialize, serde::Deserialize)]
pub enum PwmMessage {
    ConfigFanSpeed(FanSpeed),
}

/// Placeholder enum, pwm system does not need a reply for now
#[derive(serde::Serialize, serde::Deserialize)]
pub enum PwmReply {
    Success,
}

impl MessageSend for PwmMessage {
    type Label = u64;

    type Error = MicrokitError;

    fn write_message(self, buf: &mut [u8]) -> Result<(Self::Label, usize), Self::Error> {
        let len: usize =
            bincode::serde::encode_into_slice(self, buf, bincode::config::standard()).unwrap();
        // The label is unused as serde has done everything for me
        Ok((0, len))
    }
}

impl MessageRecv for PwmMessage {
    type Label = u64;

    type Error = MicrokitError;

    fn read_message(_label: Self::Label, buf: &[u8]) -> Result<Self, Self::Error> {
        let (res, _len) =
            bincode::serde::decode_from_slice::<PwmMessage, _>(buf, bincode::config::standard())
                .unwrap();
        Ok(res)
    }
}

impl MessageSend for PwmReply {
    type Label = u64;

    type Error = MicrokitError;

    fn write_message(self, buf: &mut [u8]) -> Result<(Self::Label, usize), Self::Error> {
        let len: usize =
            bincode::serde::encode_into_slice(self, buf, bincode::config::standard()).unwrap();
        // The label is unused as serde has done everything for me
        Ok((0, len))
    }
}

impl MessageRecv for PwmReply {
    type Label = u64;

    type Error = MicrokitError;

    fn read_message(_label: Self::Label, buf: &[u8]) -> Result<Self, Self::Error> {
        let (res, _len) =
            bincode::serde::decode_from_slice::<PwmReply, _>(buf, bincode::config::standard())
                .unwrap();
        Ok(res)
    }
}

pub struct PwmFan {
    channel: sel4_microkit::Channel,
}

impl PwmFan {
    pub const fn new(server_channel: sel4_microkit::Channel) -> Self {
        PwmFan {
            channel: server_channel,
        }
    }

    /// Configures the fan's speed to a predefined level.
    ///
    /// This function takes a `FanSpeed` variant and sets the hardware PWM duty
    /// cycle to the corresponding value.
    ///
    /// # Parameters
    ///
    /// * `speed`: A `FanSpeed` enum variant representing the desired speed for the fan.
    ///
    /// # Example
    ///
    /// ```
    /// // Assuming `fan_driver` is an initialized PwmFan instance.
    /// fan_driver.config_fan_speed(FanSpeed::Medium);
    /// println!("Fan speed set to medium.");
    ///
    /// fan_driver.config_fan_speed(FanSpeed::Full);
    /// println!("Fan speed set to full.");
    /// ```
    pub fn config_fan_speed(&self, speed: FanSpeed) {
        let meg: MessageInfo = MessageInfo::send(PwmMessage::ConfigFanSpeed(speed)).unwrap();
        self.channel.pp_call(meg);
    }
}
