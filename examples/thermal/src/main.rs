#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point

use core::convert::Infallible;

use sddf_pwm::pwm::{FanSpeed, PwmFan};
use sddf_thermal::thermal::ThermalSensor;
use sel4_microkit::{debug_println, protection_domain, Channel, Handler};

const THERMAL_SENSOR_CHANNEL_INDEX: usize = 0;
const THERMAL_SENSOR_CHANNEL: Channel = sel4_microkit::Channel::new(THERMAL_SENSOR_CHANNEL_INDEX);
const PWM_FAN_CHANNEL_INDEX: usize = 1;
const PWM_FAN_CHANNEL: Channel = sel4_microkit::Channel::new(PWM_FAN_CHANNEL_INDEX);

const THERMAL_SENSOR: ThermalSensor = ThermalSensor::new(THERMAL_SENSOR_CHANNEL);
const PWM_FAN: PwmFan = PwmFan::new(PWM_FAN_CHANNEL);

/// The alarm temperature is deliberately set to a lower value for testing
const ALARM_TEMPERATURE: i32 = 35000;

#[protection_domain]
fn init() -> HandlerImpl {
    let sensor_number: u32 = THERMAL_SENSOR.get_sensor_num();
    for i in 0..sensor_number {
        let temp: i32 = THERMAL_SENSOR.get_temperature(i).unwrap();
        debug_println!(
            "Sensor {} temperature: {}.{}°C",
            i,
            temp / 1000,
            (temp % 1000 - temp % 100) / 100
        );
        THERMAL_SENSOR.set_alarm_temp(i, ALARM_TEMPERATURE).unwrap();
    }
    HandlerImpl {}
}

struct HandlerImpl {}

impl Handler for HandlerImpl {
    type Error = Infallible;
    fn notified(&mut self, channel: sel4_microkit::Channel) -> Result<(), Self::Error> {
        if channel == THERMAL_SENSOR_CHANNEL {
            PWM_FAN.config_fan_speed(FanSpeed::Full);
        } else {
            debug_println!("unexpected notification from channel {channel:?}");
        }
        Ok(())
    }
}
