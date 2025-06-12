#[derive(Debug)]
pub enum PwmError {
    EINVAL,
    ENOTIMPLEMENTED,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PwmPolarity {
    PwmPolarityNormal = 0,
    PwmPolarityInversed = 1,
}

#[derive(Debug)]
pub struct PwmState {
    // The frequency that pwm operating under
    // Not the frequency pwm output
    // When used to set the state, the frequency is
    // usually set to None as pwm cannot change the clock
    pub clock_frequency: u32,
    pub enabled: bool,
    pub polarity: PwmPolarity,
    pub period: u32,
    pub duty: u32,
}

/// @period_ns: PWM period (in nanoseconds)
/// @duty_ns: PWM duty cycle (in nanoseconds)
/// @polarity: PWM polarity
/// @enabled: PWM enabled status
#[derive(Debug)]
pub struct PwmRequest {
    pub period_ns: u32,
    pub duty_ns: u32,
    pub polarity: PwmPolarity,
}

#[derive(Debug)]
pub struct PwmRawRequest {
    pub period_cycle: u32,
    pub duty_cycle: u32,
    pub polarity: PwmPolarity,
}

pub trait PwmHal {
    fn pwm_get_state(&self) -> Result<PwmState, PwmError> {
        Err(PwmError::ENOTIMPLEMENTED)
    }

    // Send request will enable the disabled pwm automatically
    fn pwm_send_request(&mut self, request: PwmRequest) -> Result<(), PwmError> {
        Err(PwmError::ENOTIMPLEMENTED)
    }

    fn pwm_raw_request(&mut self, request: PwmRawRequest) -> Result<(), PwmError> {
        Err(PwmError::ENOTIMPLEMENTED)
    }

    fn pwm_disable(&mut self) -> Result<(), PwmError> {
        Err(PwmError::ENOTIMPLEMENTED)
    }
}
