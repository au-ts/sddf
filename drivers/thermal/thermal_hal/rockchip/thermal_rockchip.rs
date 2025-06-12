use core::ptr;

use thermal_protocol::thermal_trait::{ThermalError, ThermalHal};

use crate::{
    thermal_rockchip_const::{
        GRF_SARADC_TESTBIT, GRF_SARADC_TESTBIT_ON, GRF_TSADC_TESTBIT_H, GRF_TSADC_TESTBIT_H_ON,
        GRF_TSADC_TESTBIT_L, GRF_TSADC_VCM_EN_H, GRF_TSADC_VCM_EN_L,
    },
    thermal_rockchip_trait::{TsadcRegisterV2, TshutMode, TshutPolarity},
};

/// The lookup table for ADC-to-temperature conversion.
#[derive(Debug)]
pub(crate) struct TsadcTable {
    codes: &'static [u32], // ADC codes (unsigned, matching typical hardware output)
    temps: &'static [i32], // Temperatures in micro-Celsius (µ°C)
}

// Constants for the RK3399 ADC-to-temperature lookup table
const RK3399_CODES: &[u32] = &[
    0, 402, 410, 419, 427, 436, 444, 453, 461, 470, 478, 487, 496, 504, 513, 521, 530, 538, 547,
    555, 564, 573, 581, 590, 599, 607, 616, 624, 633, 642, 650, 659, 668, 677, 685, 0x3FF,
];

const RK3399_TEMPS: &[i32] = &[
    -40_000, -40_000, -35_000, -30_000, -25_000, -20_000, -15_000, -10_000, -5_000, 0, 5_000,
    10_000, 15_000, 20_000, 25_000, 30_000, 35_000, 40_000, 45_000, 50_000, 55_000, 60_000, 65_000,
    70_000, 75_000, 80_000, 85_000, 90_000, 95_000, 100_000, 105_000, 110_000, 115_000, 120_000,
    125_000, 125_000,
];

/// The RK3399 ADC-to-temperature lookup table.
pub(crate) const RK3399_CODE_TABLE: TsadcTable = TsadcTable {
    codes: RK3399_CODES,
    temps: RK3399_TEMPS,
};

#[inline]
pub fn process_wait_unreliable(time_ns: u64) {
    for _ in 0..time_ns {
        core::hint::spin_loop(); // Use spin loop hint to reduce contention during the wait
    }
}

impl TsadcTable {
    pub(crate) fn rk_tsadc_code_to_temp(&self, code: u32) -> Result<i32, ThermalError> {
        let index: usize = self.codes.partition_point(|x| x < &code);

        // If the index is out of range, code input is invalid
        if index >= self.codes.len() {
            return Err(ThermalError::EINVAL);
        }

        let code_high: u32 = self.codes[index];

        // If code matches or index is 0, just return the temperature of the entry
        if code_high == code || index == 0 {
            return Ok(self.temps[index]);
        }

        let temp_high: i32 = self.temps[index];

        let code_low: u32 = self.codes[index - 1];
        let temp_low: i32 = self.temps[index - 1];

        // sel4_microkit::debug_println!("The temp low/high: {}/{}, code low/high: {}/{}", temp_low, temp_high, code_low, code_high);

        // I am pretty sure there cannot be code high than 0x7FFFFFFF so there should be no risk in i32 to u32 conversion
        let temp: i32 = temp_low
            + (temp_high - temp_low) * (code as i32 - code_low as i32)
                / (code_high as i32 - code_low as i32);

        Ok(temp)
    }

    pub(crate) fn rk_tsadc_temp_to_code(&self, temp: i32) -> Result<u32, ThermalError> {
        let index: usize = self.temps.partition_point(|x| x < &temp);

        // If the index is out of range, code input is invalid
        if index >= self.temps.len() {
            return Err(ThermalError::EINVAL);
        }

        let temp_high: i32 = self.temps[index];

        // If temperature matches or code index is 0, just return the code of the entry
        if temp_high == temp || index == 0 {
            return Ok(self.codes[index]);
        }

        let code_high: u32 = self.codes[index];

        let code_low: u32 = self.codes[index - 1];
        let temp_low: i32 = self.temps[index - 1];

        // sel4_microkit::debug_println!("The temp low/high: {}/{}, code low/high: {}/{}", temp_low, temp_high, code_low, code_high);

        // I am pretty sure there cannot be code high than 0x7FFFFFFF...
        let code: u32 = (code_low as i32
            + (code_high as i32 - code_low as i32) * (temp - temp_low) / (temp_high - temp_low))
            as u32;

        Ok(code)
    }
}

pub struct RK3399ThermalHardware {
    register: &'static mut TsadcRegisterV2,
}

const RK3399_CHANNEL_NUM: u32 = 2;
const RK3399_WRITE_MASK: u32 = 16;
const GRF_ADDR: u32 = 0xFF77_0000;
const CRU_ADDR: u32 = 0xFF76_0000;
const CRU_SOFTRST_CON13: u32 = CRU_ADDR + 0x434;
const CRU_SOFTRST_CON14: u32 = CRU_ADDR + 0x438;
const CRU_CLKSEL_CON27: u32 = CRU_ADDR + 0x16c;
// Control if the clk to tsadc is gated
const CRU_CLKGATE_CON9: u32 = CRU_ADDR + 0x324;
// Control if the pclk to tsadc is gated
const CRU_CLKGATE_CON22: u32 = CRU_ADDR + 0x358;
const CRU_TSADC_24M_CLK: u32 = 0x3FF001F;
const CRU_CLK_TSADC_SRC_GATE: u32 = 1 << 10;
const CRU_CLK_PCLK_TSADC_GATE: u32 = 1 << 13;

const GPIO1_ADDR: u32 = 0xFF32_0000;
const GPIO1A6_SEL: u32 = GPIO1_ADDR + 0x10;
const GPIO1A6_DISABLE: u32 = 0x30000000;
const GPIO1_A6_TSADC_INT: u32 = 0x30003000;
const GPIO1A_P: u32 = GPIO1_ADDR + 0x50;
const GPIO1A_P_DISABLE: u32 = 0x30000000;

// CLock name clk_tsadc, ID 166
impl RK3399ThermalHardware {
    pub unsafe fn new() -> Self {
        let mut hal: RK3399ThermalHardware = RK3399ThermalHardware {
            register: &mut *(0xff260000 as *mut TsadcRegisterV2),
        };

        hal.rk3399_tsadc_setup(GRF_ADDR);

        hal
    }

    /// This function is unsafe because the potential race condition as the function
    /// writing directly to the registers in clock subsystem
    unsafe fn rk3399_tsadc_reset() {
        unsafe {
            core::ptr::write_volatile(CRU_SOFTRST_CON14 as *mut u32, 0x1000100);
        }

        process_wait_unreliable(50_000);

        unsafe {
            core::ptr::write_volatile(CRU_SOFTRST_CON14 as *mut u32, 0x1000000);
        }

        process_wait_unreliable(100_000);
    }

    /// This function is unsafe because the potential race condition as the function
    /// writing directly to the registers in gpio, grf and clk subsystems
    /// I need to do the follow to init the system properly:
    /// 1. Check the pinctrl in the device tree to see if they have been configured correctly
    /// 2. Assert presetn_tsadc_req in CRU_SOFTRST_CON13 and after 20 microseconds, deassert it.
    /// 3. Initialize with high TshutPolarity
    /// Maybe select good clk source as well? CRU_CLKSEL_CON27
    /// RK_PA6 in the device tree is correspond to gpio1a6, check gpio1a6_sel in datasheet
    unsafe fn rk3399_tsadc_setup(&mut self, grf_base: u32) {
        // GPIO1A6_SEL is for disable the shutdown during setup process, GPIO1A_P is unknown but Linux did this
        unsafe {
            core::ptr::write_volatile(GPIO1A6_SEL as *mut u32, GPIO1A6_DISABLE);

            core::ptr::write_volatile(GPIO1A_P as *mut u32, GPIO1A_P_DISABLE);
        }

        // Set good clk freq for tsadc
        unsafe {
            core::ptr::write_volatile(CRU_CLKSEL_CON27 as *mut u32, CRU_TSADC_24M_CLK);
        }

        unsafe {
            // The upper 16 bits of the 32 bit register is the protection bits
            core::ptr::write_volatile(
                CRU_CLKGATE_CON9 as *mut u32,
                CRU_CLK_TSADC_SRC_GATE << RK3399_WRITE_MASK,
            );

            core::ptr::write_volatile(
                CRU_CLKGATE_CON22 as *mut u32,
                CRU_CLK_PCLK_TSADC_GATE << RK3399_WRITE_MASK,
            );
        }

        Self::rk3399_tsadc_reset();

        unsafe {
            ptr::write_volatile(
                (grf_base + GRF_TSADC_TESTBIT_L) as *mut u32,
                GRF_TSADC_VCM_EN_L,
            );

            ptr::write_volatile(
                (grf_base + GRF_TSADC_TESTBIT_H) as *mut u32,
                GRF_TSADC_VCM_EN_H,
            );
        }

        /* The spec note says at least 15 us */
        process_wait_unreliable(20_000);

        unsafe {
            ptr::write_volatile(
                (grf_base + GRF_SARADC_TESTBIT) as *mut u32,
                GRF_SARADC_TESTBIT_ON,
            );

            ptr::write_volatile(
                (grf_base + GRF_TSADC_TESTBIT_H) as *mut u32,
                GRF_TSADC_TESTBIT_H_ON,
            );
        }

        /* The spec note says at least 90 us */
        process_wait_unreliable(100_000);

        self.register.initialize(TshutPolarity::TshutHighActive);

        self.register.set_tshut_mode(TshutMode::TshutModeGpio);

        let tshut_code: u32 = RK3399_CODE_TABLE.rk_tsadc_temp_to_code(95_000).unwrap();

        for i  in 0..RK3399_CHANNEL_NUM {
            self.register.set_tshut_temp(i as usize, tshut_code);
        }

        self.register.control(true);

        // Turn on GPIO pins for reset the board
        unsafe {
            core::ptr::write_volatile(GPIO1A6_SEL as *mut u32, GPIO1_A6_TSADC_INT);

            core::ptr::write_volatile(GPIO1A_P as *mut u32, GPIO1A_P_DISABLE);
        }
    }
}

impl ThermalHal for RK3399ThermalHardware {
    fn thermal_sensor_get_sensor_number(&self) -> Result<u32, ThermalError>  {
        Ok(RK3399_CHANNEL_NUM)
    }

    fn thermal_get_tempareture(&self, channel: u32) -> Result<i32, ThermalError> {
        if channel >= RK3399_CHANNEL_NUM {
            return Err(ThermalError::EINVAL);
        }
        RK3399_CODE_TABLE.rk_tsadc_code_to_temp(self.register.get_temp(channel as usize))
    }

    fn thermal_set_trip(&mut self, channel: u32, alarm_temperature: i32) -> Result<(), ThermalError> {
        if channel >= RK3399_CHANNEL_NUM {
            return Err(ThermalError::EINVAL);
        }
        let temp_code: u32 = RK3399_CODE_TABLE.rk_tsadc_temp_to_code(alarm_temperature)?;
        self.register.set_alarm_temp(channel as usize, temp_code);
        Ok(())
    }

    fn thermal_ack_irq(&mut self) -> Result<(), ThermalError> {
        self.register.irq_ack();
        Ok(())
    }
}
