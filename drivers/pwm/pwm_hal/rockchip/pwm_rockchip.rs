use core::ptr;

use pwm_protocol::pwm_trait::{PwmError, PwmHal, PwmPolarity, PwmRawRequest, PwmState};

// Define the register offsets as a struct
#[derive(Debug)]
struct PwmRegisters {
    cntr: u32,   // Counter register offset
    period: u32, // Period register offset
    duty: u32,   // Duty cycle register offset
    ctrl: u32,   // Control register offset
}

// Define the PWM data structure
struct RockchipPwmData {
    regs: PwmRegisters,
    prescaler: u32,
    supports_polarity: bool,
    supports_lock: bool,
    enable_conf: u32, // Bitmask for control register
}

#[derive(Debug)]
pub struct RockchipPwmHardware {
    reg_base: u32,
    enabled: bool,
    polarity: PwmPolarity,
    period: u32,
    duty: u32,
}

// Addr for manipulating the pinctrl and gpio manually
const GRF_ADDR: u32 = 0xFF770000;
const GRF_GPIO4C_IOMUX_OFFSET: u32 = 0x0e028;
const GRF_GPIO4C_IOMUX_ADDR: u32 = GRF_ADDR + GRF_GPIO4C_IOMUX_OFFSET;
const GRF_GPIO4C3_SEL: u32 = 0b11 << 12;
const GRF_GPIO4_C3_PWM_1: u32 = 0b01 << 12;
const GRF_WRITE_ENABLE_MASK: u32 = (0b11 << 12) << 16;

const GRF_GPIO4C_P_OFFSET: u32 = 0x0e068;
const GRF_GPIO4C_P_ADDR: u32 = GRF_ADDR + GRF_GPIO4C_P_OFFSET;
const GRF_GPIO4C3_P: u32 = 0b11 << 12;
const GRF_GPIO4_C3_PULL_DOWN: u32 = 0b10 << 12;

// From pwm-rockchip.c (likely in a header or inline)
// Control register bit definitions
const PWM_CTRL_TIMER_EN: u32 = 1 << 0; // Bit 0: Enable the PWM timer
const PWM_CTRL_OUTPUT_EN: u32 = 1 << 3; // Bit 3: Enable PWM output

// PWM-specific flags (used in pwm_data_v3.enable_conf)
const PWM_ENABLE: u32 = 1 << 0; // Bit 0: Enable PWM (same as PWM_CTRL_TIMER_EN)
const PWM_CONTINUOUS: u32 = 1 << 1; // Bit 1: Continuous mode (vs one-shot)
const PWM_DUTY_POSITIVE: u32 = 1 << 3; // Bit 3: Duty cycle is positive (active-high)
const PWM_DUTY_NEGATIVE: u32 = 0 << 3; // Bit 3: Duty cycle is negative (active-low, no shift needed)
const PWM_INACTIVE_NEGATIVE: u32 = 0 << 4; // Bit 4: Inactive state is negative (low)
const PWM_INACTIVE_POSITIVE: u32 = 1 << 4; // Bit 4: Inactive state is positive (high)
const PWM_POLARITY_MASK: u32 = PWM_DUTY_POSITIVE | PWM_INACTIVE_POSITIVE; // Mask for polarity bits (3 and 4)
const PWM_OUTPUT_LEFT: u32 = 0 << 5; // Bit 5: Output left-aligned (default, no shift)
const PWM_LOCK_EN: u32 = 1 << 6; // Bit 6: Lock PWM configuration
const PWM_LP_DISABLE: u32 = 0 << 8; // Bit 8: Disable low-power mode (0 = disabled)

// The value I am guessing the clock rate to be
// If the div is touched, the driver may not work
// As the clock rate could be different from this value
// const RK3399_PWM_CLOCKRATE: u32 = 24_000_000;
const RK3399_PWM_CLOCKRATE: u32 = 100_000_000;

// Equivalent to pwm_data_v2 in Linux
// Compatible with "rockchip,rk3399-pwm", "rockchip,rk3288-pwm"
const PWM_DATA: RockchipPwmData = RockchipPwmData {
    regs: PwmRegisters {
        cntr: 0x00,
        period: 0x04,
        duty: 0x08,
        ctrl: 0x0c,
    },
    prescaler: 1,
    supports_polarity: true,
    supports_lock: false,
    enable_conf: PWM_OUTPUT_LEFT | PWM_LP_DISABLE | PWM_ENABLE | PWM_CONTINUOUS,
};

impl RockchipPwmHardware {
    /// This function is unsafe as creating multiple RockchipPwmHardware with the same reg base could cause problems
    pub unsafe fn new(register_base: u32) -> Self {
        let mut hardware: RockchipPwmHardware = RockchipPwmHardware {
            reg_base: register_base,
            enabled: false,
            period: 0,
            duty: 0,
            // The polarity is actually in undefined status here
            // But it would be set to a valid state when receive first request
            polarity: PwmPolarity::PwmPolarityNormal,
        };

        let _ = hardware.pwm_disable();

        Self::pwm_iomux_config();

        hardware
    }

    fn pwm_iomux_config() {
        // Configure IOMUX register
        unsafe {
            let value: u32 = ptr::read_volatile(GRF_GPIO4C_IOMUX_ADDR as *const u32);

            let write_enable_value: u32 = value | GRF_WRITE_ENABLE_MASK;

            ptr::write_volatile(GRF_GPIO4C_IOMUX_ADDR as *mut u32, write_enable_value);

            let modified_value: u32 = (write_enable_value & !GRF_GPIO4C3_SEL) | GRF_GPIO4_C3_PWM_1;

            ptr::write_volatile(GRF_GPIO4C_IOMUX_ADDR as *mut u32, modified_value);

            let final_value: u32 = (value & 0xFFFF0000) | (modified_value & 0x0000FFFF);

            ptr::write_volatile(GRF_GPIO4C_IOMUX_ADDR as *mut u32, final_value);
        }

        // Configure pull-up/down register
        unsafe {
            let value: u32 = ptr::read_volatile(GRF_GPIO4C_P_ADDR as *const u32);

            let write_enable_value: u32 = value | GRF_WRITE_ENABLE_MASK;

            ptr::write_volatile(GRF_GPIO4C_P_ADDR as *mut u32, write_enable_value);

            let modified_value: u32 =
                (write_enable_value & !GRF_GPIO4C3_P) | GRF_GPIO4_C3_PULL_DOWN;

            ptr::write_volatile(GRF_GPIO4C_P_ADDR as *mut u32, modified_value);

            let final_value: u32 = (value & 0xFFFF0000) | (modified_value & 0x0000FFFF);

            ptr::write_volatile(GRF_GPIO4C_P_ADDR as *mut u32, final_value);
        }
    }

    /*
    fn clock_probe() {
        pclk_rkpwm_pmu
    }
     */
}

impl PwmHal for RockchipPwmHardware {
    fn pwm_get_state(&self) -> Result<PwmState, PwmError> {
        Ok(PwmState {
            enabled: self.enabled,
            clock_frequency: RK3399_PWM_CLOCKRATE / PWM_DATA.prescaler,
            period: self.period,
            duty: self.duty,
            polarity: self.polarity.clone(),
        })
    }

    fn pwm_raw_request(&mut self, request: PwmRawRequest) -> Result<(), PwmError> {
        let mut enable_pwm: bool = !self.enabled;

        let mut ctrl: u32 = PWM_DATA.enable_conf;

        if enable_pwm == true || request.polarity != self.polarity {
            enable_pwm = true;
            if PWM_DATA.supports_polarity == false && request.polarity != self.polarity {
                return Err(PwmError::EINVAL);
            } else {
                ctrl &= !PWM_POLARITY_MASK;
                if request.polarity == PwmPolarity::PwmPolarityNormal {
                    ctrl |= PWM_DUTY_POSITIVE | PWM_INACTIVE_NEGATIVE;
                } else {
                    ctrl |= PWM_DUTY_NEGATIVE | PWM_INACTIVE_POSITIVE;
                }
                self.polarity = request.polarity;
            }
        }

        unsafe {
            ptr::write_volatile(
                (self.reg_base + PWM_DATA.regs.period) as *mut u32,
                request.period_cycle,
            );

            // Configure duty
            ptr::write_volatile(
                (self.reg_base + PWM_DATA.regs.duty) as *mut u32,
                request.duty_cycle,
            );
        }

        if enable_pwm == true {
            unsafe {
                // Enable the pwm first if not enabled
                ptr::write_volatile((self.reg_base + PWM_DATA.regs.ctrl) as *mut u32, ctrl);
            }
            self.enabled = true;
        }

        Ok(())
    }

    fn pwm_disable(&mut self) -> Result<(), PwmError> {
        unsafe {
            // Reset control register first
            ptr::write_volatile((self.reg_base + PWM_DATA.regs.ctrl) as *mut u32, 0);

            ptr::write_volatile((self.reg_base + PWM_DATA.regs.duty) as *mut u32, 0);

            ptr::write_volatile((self.reg_base + PWM_DATA.regs.period) as *mut u32, 0);
        }

        self.enabled = false;
        self.duty = 0;
        self.period = 0;
        self.polarity = PwmPolarity::PwmPolarityNormal;

        Ok(())
    }
}
