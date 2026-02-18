use core::ptr;

use sel4_microkit::debug_println;
use thermal_protocol::thermal_trait::ThermalError;

use crate::thermal_rockchip_const::{
    TSADCV2_AUTO_EN, TSADCV2_AUTO_TSHUT_POLARITY_HIGH, TSADCV2_HIGHT_INT_DEBOUNCE_COUNT,
    TSADCV2_HIGHT_TSHUT_DEBOUNCE_COUNT, TSADCV3_AUTO_PERIOD_HT_TIME, TSADCV3_AUTO_PERIOD_TIME,
    TSADCV3_AUTO_Q_SEL_EN, TSADCV3_INT_PD_CLEAR_MASK,
};

/// The system Temperature Sensors tshut(tshut) polarity
/// the bit 8 is tshut polarity.
/// 0: low active, 1: high active
pub(crate) enum TshutPolarity {
    TshutLowActive = 0,
    TshutHighActive = 1,
}

pub(crate) enum TshutMode {
    TshutModeCru = 0,
    TshutModeGpio = 1,
}

// Constants for TSADC register offsets (adapted from Linux)
const TSADCV2_USER_CON: u32 = 0x00;
const TSADCV2_AUTO_CON: u32 = 0x04;
const TSADCV2_INT_EN: u32 = 0x08;
const TSADCV2_INT_PD: u32 = 0x0c;
const TSADCV2_DATA: u32 = 0x20;
const TSADCV2_COMP_INT: u32 = 0x30;
const TSADCV2_COMP_SHUT: u32 = 0x40;
const TSADCV2_HIGHT_INT_DEBOUNCE: u32 = 0x60;
const TSADCV2_HIGHT_TSHUT_DEBOUNCE: u32 = 0x64;
const TSADCV2_AUTO_PERIOD: u32 = 0x68;
const TSADCV2_AUTO_PERIOD_HT: u32 = 0x6c;

const TSADCV3_AUTO_SRC_CON: u32 = 0x0c;
const TSADCV3_HT_INT_EN: u32 = 0x14;
const TSADCV3_HSHUT_GPIO_INT_EN: u32 = 0x18;
const TSADCV3_HSHUT_CRU_INT_EN: u32 = 0x1c;
const TSADCV3_INT_PD: u32 = 0x24;
const TSADCV3_HSHUT_PD: u32 = 0x28;
const TSADCV3_HIGHT_INT_DEBOUNCE: u32 = 0x14c;
const TSADCV3_HIGHT_TSHUT_DEBOUNCE: u32 = 0x150;
const TSADCV3_AUTO_PERIOD: u32 = 0x154;
const TSADCV3_AUTO_PERIOD_HT: u32 = 0x158;

const TSHUT_2CRU_EN_SRC: u32 = 0x300;
const TSHUT_2GPIO_EN_SRC: u32 = 0x30;

const TSHUT_SRC0_EN: u32 = 0x10;

const HT_INTEN_SRC0: u32 = 0x1;

/// The register structure for tsadc
/// It is labeled as V2 as more than one board use similiar register mapping
/// with rk3399 being one of them. And V2 means it is the same register struct
/// in Linux source code rockchip_thermal.c that labeled as V2
/// Check Linux source code for more details
#[repr(C)]
pub struct TsadcRegisterV2 {
    // 0x00, The control register of A/D Converter.
    user_con: u32,
    // 0x04, TSADC auto mode control register
    auto_con: u32,
    // 0x08, Interrupt control register
    int_en: u32,
    // 0x0C, Interrupt status register
    int_pd: u32,
    // 0x10-0x1C, Padding for other unused device memory
    _reserved0: [u32; 4],
    // 0x20-0x2C, This register contains the data after A/D Conversion for channel 1-4.
    tsadc_data: [u32; 4],
    // 0x30-0x3C, TSADC high temperature level for channel 1-4
    tsadc_comp_int: [u32; 4],
    // 0x40-0x4C, TSADC shutdown temperature level for channel 1-4
    tsadc_comp_shut: [u32; 4],
    // 0x50-0x5C, Padding for other unused device memory
    _reserved1: [u32; 4],
    // 0x60, High temperature debounce
    hight_int_debounce: u32,
    // 0x64, Shutdown temperature debounce
    hight_tshut_debounce: u32,
    // 0x68, TSADC auto access period
    auto_period: u32,
    // 0x6c, TSADC auto access period when temperature is high
    auto_period_ht: u32,
    // 0x80, TSADC low temperature level for channel 1-2
    comp_low_int: [u32; 2],
}

impl TsadcRegisterV2 {
    // Current initizalization assume the grf is available but is not initialized by the function
    // However, in reality there seems to be board that is not open to public like RK3366 that does not have GRF access
    pub fn initialize(&mut self, tshut_polarity: TshutPolarity) {
        unsafe {
            ptr::write_volatile(&mut self.auto_period, TSADCV3_AUTO_PERIOD_TIME);

            ptr::write_volatile(
                &mut self.hight_int_debounce,
                TSADCV2_HIGHT_INT_DEBOUNCE_COUNT,
            );

            ptr::write_volatile(&mut self.auto_period_ht, TSADCV3_AUTO_PERIOD_HT_TIME);

            ptr::write_volatile(
                &mut self.hight_tshut_debounce,
                TSADCV2_HIGHT_TSHUT_DEBOUNCE_COUNT,
            );
        }

        if let TshutPolarity::TshutHighActive = tshut_polarity {
            unsafe {
                ptr::write_volatile(&mut self.auto_con, 0u32 | TSADCV2_AUTO_TSHUT_POLARITY_HIGH);
            }
        } else {
            unsafe {
                ptr::write_volatile(&mut self.auto_con, 0u32 & !TSADCV2_AUTO_TSHUT_POLARITY_HIGH);
            }
        }
    }

    pub fn get_temp(&self, channel: usize) -> u32 {
        unsafe { ptr::read_volatile(&self.tsadc_data[channel]) }
    }

    pub fn set_alarm_temp(&mut self, channel: usize, temp_code: u32) {
        unsafe { ptr::write_volatile(&mut self.tsadc_comp_int[channel], temp_code) }

        let mut val: u32 = unsafe { ptr::read_volatile(&self.int_en) };

        val |= HT_INTEN_SRC0 << channel;

        unsafe { ptr::write_volatile(&mut self.int_en, val) }
    }

    pub fn set_tshut_temp(&mut self, channel: usize, temp_code: u32) {
        unsafe { ptr::write_volatile(&mut self.tsadc_comp_shut[channel], temp_code) }

        let mut val: u32 = unsafe { ptr::read_volatile(&self.auto_con) };

        val |= TSHUT_SRC0_EN << channel;

        unsafe { ptr::write_volatile(&mut self.auto_con, val) }
    }

    pub fn set_tshut_mode(&mut self, mode: TshutMode) {
        let mut val: u32 = unsafe { ptr::read_volatile(&self.int_en) };

        match mode {
            TshutMode::TshutModeCru => {
                val &= !(TSHUT_2GPIO_EN_SRC);
                val |= TSHUT_2CRU_EN_SRC;
            }
            TshutMode::TshutModeGpio => {
                val &= !(TSHUT_2CRU_EN_SRC);
                val |= TSHUT_2GPIO_EN_SRC;
            }
        }
        unsafe {
            ptr::write_volatile(&mut self.int_en, val);
        }
    }

    #[inline]
    pub fn irq_ack(&mut self) {
        let val: u32 = unsafe { ptr::read_volatile(&self.int_pd) };

        unsafe {
            ptr::write_volatile(&mut self.int_pd, val & TSADCV3_INT_PD_CLEAR_MASK);
        }
    }

    #[inline]
    pub fn control(&mut self, enable: bool) {
        let mut val: u32 = unsafe { ptr::read_volatile(&self.auto_con) };

        if enable {
            val |= TSADCV2_AUTO_EN | TSADCV3_AUTO_Q_SEL_EN;
        } else {
            val &= !TSADCV2_AUTO_EN;
        }

        unsafe {
            ptr::write_volatile(&mut self.auto_con, val);
        }
    }
}
