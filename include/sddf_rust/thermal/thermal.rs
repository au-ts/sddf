use sel4_microkit::MessageInfo;
use sel4_microkit_message::{
    types::{MessageRecv, MessageSend},
    MessageInfoExt,
};

use crate::error::error::MicrokitError;

#[derive(serde::Serialize, serde::Deserialize)]
pub enum ThermalMessage {
    GetSensorNum,
    GetTemp(u32),
    SetAlarmTemp(u32, i32),
}

#[derive(serde::Serialize, serde::Deserialize)]
pub enum ThermalReply {
    SensorNum(u32),
    Temp(Result<i32, MicrokitError>),
    AlarmTemp(Result<(), MicrokitError>),
}

/// Using enum with types make things much difficult for C users
/// But for now, I will still use it for learning purpose
impl MessageSend for ThermalMessage {
    type Label = u64;

    type Error = MicrokitError;

    fn write_message(self, buf: &mut [u8]) -> Result<(Self::Label, usize), Self::Error> {
        let len: usize =
            bincode::serde::encode_into_slice(self, buf, bincode::config::standard()).unwrap();
        // The label is unused as serde has done everything for me
        Ok((0, len))
    }
}

impl MessageRecv for ThermalMessage {
    type Label = u64;

    type Error = MicrokitError;

    fn read_message(_label: Self::Label, buf: &[u8]) -> Result<Self, Self::Error> {
        let (res, _len) = bincode::serde::decode_from_slice::<ThermalMessage, _>(
            buf,
            bincode::config::standard(),
        )
        .unwrap();
        Ok(res)
    }
}

impl MessageSend for ThermalReply {
    type Label = u64;

    type Error = MicrokitError;

    fn write_message(self, buf: &mut [u8]) -> Result<(Self::Label, usize), Self::Error> {
        let len: usize =
            bincode::serde::encode_into_slice(self, buf, bincode::config::standard()).unwrap();
        // The label is unused as serde has done everything for me
        Ok((0, len))
    }
}

impl MessageRecv for ThermalReply {
    type Label = u64;

    type Error = MicrokitError;

    fn read_message(_label: Self::Label, buf: &[u8]) -> Result<Self, Self::Error> {
        let (res, _len) =
            bincode::serde::decode_from_slice::<ThermalReply, _>(buf, bincode::config::standard())
                .unwrap();
        Ok(res)
    }
}

pub struct ThermalSensor {
    channel: sel4_microkit::Channel,
}

impl ThermalSensor {
    pub const fn new(server_channel: sel4_microkit::Channel) -> Self {
        ThermalSensor {
            channel: server_channel,
        }
    }

    /// Returns the total number of available thermal sensor channels.
    ///
    /// This can be used to iterate over all available sensors to read their
    /// temperatures or configure their settings. The channels are typically
    /// zero-indexed (i.e., from `0` to `get_sensor_num() - 1`).
    ///
    /// # Returns
    ///
    /// A `u32` representing the count of available sensor channels.
    ///
    /// # Example
    ///
    /// ```
    /// // Assuming `thermal_sensor` is an initialized ThermalSensor instance.
    /// let num_sensors = thermal_sensor.get_sensor_num();
    /// println!("This device has {} thermal sensors.", num_sensors);
    /// ```
    pub fn get_sensor_num(&self) -> u32 {
        let meg: MessageInfo = MessageInfo::send(ThermalMessage::GetSensorNum).unwrap();

        let reply: ThermalReply = self.channel.pp_call(meg).recv::<ThermalReply>().unwrap();

        if let ThermalReply::SensorNum(num) = reply {
            return num;
        } else {
            panic!("Thermal reply is not about Sensor numbers!")
        }
    }

    /// Reads the temperature from a specific sensor channel.
    ///
    /// The temperature is returned in milli-Celsius (°C * 1000) to provide
    /// high precision without using floating-point numbers.
    ///
    /// # Parameters
    ///
    /// * `sensor_channel`: The zero-based index of the sensor channel to read. This
    ///   should be less than the value returned by `get_sensor_num()`.
    ///
    /// # Returns
    ///
    /// * `Ok(i32)`: The temperature of the specified channel in milli-Celsius.
    /// * `Err(MicrokitError)`: An error if the `sensor_channel` is invalid or a
    ///   hardware communication error occurs.
    ///
    /// # Example
    ///
    /// ```
    /// // Assuming `thermal_sensor` is an initialized ThermalSensor instance.
    /// let channel = 0;
    /// match thermal_sensor.get_temperature(channel) {
    ///     Ok(temp_mc) => {
    ///         println!("Sensor {}: {} m°C ({}°C)",
    ///             channel,
    ///             temp_mc,
    ///             temp_mc / 1000
    ///         );
    ///     }
    ///     Err(e) => {
    ///         println!("Failed to read temperature from sensor {}: {:?}", channel, e);
    ///     }
    /// }
    /// ```
    pub fn get_temperature(&self, sensor_channel: u32) -> Result<i32, MicrokitError> {
        let meg: MessageInfo = MessageInfo::send(ThermalMessage::GetTemp(sensor_channel)).unwrap();

        let reply: ThermalReply = self.channel.pp_call(meg).recv::<ThermalReply>().unwrap();

        if let ThermalReply::Temp(temp) = reply {
            return temp;
        } else {
            panic!("Thermal reply does not contain temperature!")
        }
    }

    /// Sets the high-temperature alarm threshold for a specific sensor channel.
    ///
    // When the sensor's reading surpasses this value, the driver will issue a
    /// notification to the system's governor. The temperature must be specified
    /// in milli-Celsius.
    ///
    /// # Parameters
    ///
    /// * `sensor_channel`: The zero-based index of the sensor channel to configure.
    /// * `alarm_temp`: The temperature threshold in milli-Celsius. If the sensor
    ///   reading exceeds this value, an alarm notification will be triggered.
    ///
    /// # Returns
    ///
    /// * `Ok(())`: On successful configuration of the alarm.
    /// * `Err(MicrokitError)`: An error if the `sensor_channel` is invalid, the
    ///   `alarm_temp` is out of the hardware's supported range, or a hardware
    ///   communication error occurs.
    ///
    /// # Example
    ///
    /// ```
    /// // Assuming `thermal_sensor` is an initialized ThermalSensor instance.
    /// let cpu_sensor_channel = 0;
    /// let critical_temp_mc = 95_000; // 95.0°C
    ///
    /// match thermal_sensor.set_alarm_temp(cpu_sensor_channel, critical_temp_mc) {
    ///     Ok(()) => {
    ///         println!("Alarm for sensor {} set to {} m°C.", cpu_sensor_channel, critical_temp_mc);
    ///     }
    ///     Err(e) => {
    ///         println!("Failed to set alarm for sensor {}: {:?}", cpu_sensor_channel, e);
    ///     }
    /// }
    /// ```
    pub fn set_alarm_temp(
        &self,
        sensor_channel: u32,
        alarm_temp: i32,
    ) -> Result<(), MicrokitError> {
        let meg: MessageInfo =
            MessageInfo::send(ThermalMessage::SetAlarmTemp(sensor_channel, alarm_temp)).unwrap();

        let reply: ThermalReply = self.channel.pp_call(meg).recv::<ThermalReply>().unwrap();

        if let ThermalReply::AlarmTemp(res) = reply {
            return res;
        } else {
            panic!("Thermal reply does not contain temperature!")
        }
    }
}
