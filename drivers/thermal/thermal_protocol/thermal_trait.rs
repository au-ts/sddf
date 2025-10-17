#[derive(Debug)]
pub enum ThermalError {
    EINVAL,
    ENOTIMPLEMENTED,
}

/*
struct ThermalSensor {
    /// Temperature of this sensor, in miliCelsius
    temperature: i32,
    /// Temperature that cause the temperature to send warning
    /// If it is None, then the temperature is not set
    /// for the respective sensor
    /// The governor should be allowed to set this value
    /// If it is set, the governor will receive notification
    /// if the temperature exceed this value
    alarm_temperature: Option<i32>,
    /// Temperature that cause the board to shut down or reset
    /// If it is None, such shut down temperature does not exist
    /// The upper layer should not be able to set this value
    shutdown_temperature: Option<i32>,
}
*/

pub trait ThermalHal {
    /// Read back how many thermal sensors there are on the computer
    fn thermal_sensor_get_sensor_number(&self) -> Result<u32, ThermalError> {
        Err(ThermalError::ENOTIMPLEMENTED)
    }

    /// Read back the temperature from a specific sensor number
    fn thermal_get_tempareture(&self, channel: u32) -> Result<i32, ThermalError> {
        Err(ThermalError::ENOTIMPLEMENTED)
    }

    /// Optional method for thermal sensor do automatical temperature reading.
    /// Set alarm temperature for specific driver
    fn thermal_set_trip(
        &mut self,
        channel: u32,
        alarm_temperature: i32,
    ) -> Result<(), ThermalError> {
        Err(ThermalError::ENOTIMPLEMENTED)
    }

    /// Optional method for thermal sensor uses automatical temperature reading and generate irq for alarm
    fn thermal_ack_irq(&mut self) -> Result<(), ThermalError> {
        Err(ThermalError::ENOTIMPLEMENTED)
    }
}
