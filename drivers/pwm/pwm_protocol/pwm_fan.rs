use crate::pwm_trait::{PwmError, PwmHal, PwmPolarity, PwmRawRequest, PwmState};

// Well, most of the fan should be falling in the range
// But could there be weird fans???
const COMMON_FAN_FREQ: u32 = 25_000;
const MINIMUM_FAN_FREQ: u32 = 20_000;

const UPPER_FAN_FREQ: u32 = 50_000;

pub struct Fan<T: PwmHal> {
    pwm: T,
}

#[repr(u8)]
pub enum FanSpeed {
    Stopped = 0,  // 0%   (0/255)
    Low = 64,     // ~25% (64/255)
    Medium = 128, // ~50% (128/255)
    High = 192,   // ~75% (192/255)
    Full = 255,   // 100% (255/255)
}

impl<T: PwmHal> Fan<T> {
    // Make sure your pwm is indeed control a fan to avoid damaging hardware
    pub fn new(pwm: T) -> Self {
        Fan { pwm }
    }

    pub fn config_fan_speed(&mut self, speed: FanSpeed) -> Result<(), PwmError> {
        match speed {
            // Disable the PWM if fan is stopped
            FanSpeed::Stopped => self.pwm.pwm_disable(),
            _ => {
                let status: PwmState = self.pwm.pwm_get_state()?;
                // Figure out if it is PWM signal being too slow
                let period: u32 = status.clock_frequency / COMMON_FAN_FREQ;
                let duty: u32 = (period * (speed as u32)) / (FanSpeed::Full as u32);
                let state: PwmRawRequest = PwmRawRequest {
                    polarity: PwmPolarity::PwmPolarityNormal,
                    period_cycle: period,
                    duty_cycle: duty,
                };
                self.pwm.pwm_raw_request(state)
            }
        }
    }
}
