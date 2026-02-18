// Bit manipulation constants for TSADCV2
pub const TSADCV2_AUTO_EN: u32 = 1 << 0; // Bit 0
pub const TSADCV2_AUTO_EN_MASK: u32 = 1 << 16; // Bit 16
pub const TSADCV2_AUTO_TSHUT_POLARITY_HIGH: u32 = 1 << 8; // Bit 8
pub const TSADCV2_AUTO_TSHUT_POLARITY_MASK: u32 = 1 << 24; // Bit 24

// TSADCV2 channel-specific bit manipulations
#[inline]
pub const fn tsadcv2_auto_src_en(chn: u32) -> u32 {
    1 << (4 + chn) // Bit (4 + chn)
}

#[inline]
pub const fn tsadcv2_int_src_en(chn: u32) -> u32 {
    1 << chn // Bit chn
}

#[inline]
pub const fn tsadcv2_int_src_en_mask(chn: u32) -> u32 {
    1 << (16 + chn) // Bit (16 + chn)
}

#[inline]
pub const fn tsadcv2_shut_2gpio_src_en(chn: u32) -> u32 {
    1 << (4 + chn) // Bit (4 + chn)
}

#[inline]
pub const fn tsadcv2_shut_2cru_src_en(chn: u32) -> u32 {
    1 << (8 + chn) // Bit (8 + chn)
}

// TSADCV3 channel-specific bit manipulations
#[inline]
pub const fn tsadcv3_auto_src_en(chn: u32) -> u32 {
    1 << chn // Bit chn
}

#[inline]
pub const fn tsadcv3_auto_src_en_mask(chn: u32) -> u32 {
    1 << (16 + chn) // Bit (16 + chn)
}

// TSADCV3-specific constant
pub const TSADCV3_AUTO_Q_SEL_EN: u32 = 1 << 1; // Bit 1

// Interrupt pending clear masks
pub const TSADCV2_INT_PD_CLEAR_MASK: u32 = !(1 << 8); // Clear bit 8
pub const TSADCV3_INT_PD_CLEAR_MASK: u32 = !(1 << 16); // Clear bit 16
pub const TSADCV4_INT_PD_CLEAR_MASK: u32 = 0xffffffff; // All bits set

// Data masks for different TSADC versions
pub const TSADCV2_DATA_MASK: u32 = 0xfff; // 12 bits
pub const TSADCV3_DATA_MASK: u32 = 0x3ff; // 10 bits
pub const TSADCV4_DATA_MASK: u32 = 0x1ff; // 9 bits

// Debounce and period constants
pub const TSADCV2_HIGHT_INT_DEBOUNCE_COUNT: u32 = 4;
pub const TSADCV2_HIGHT_TSHUT_DEBOUNCE_COUNT: u32 = 4;
pub const TSADCV2_AUTO_PERIOD_TIME: u32 = 250; // 250ms
pub const TSADCV2_AUTO_PERIOD_HT_TIME: u32 = 50; // 50ms
pub const TSADCV3_AUTO_PERIOD_TIME: u32 = 1875; // 2.5ms
pub const TSADCV3_AUTO_PERIOD_HT_TIME: u32 = 1875; // 2.5ms
pub const TSADCV5_AUTO_PERIOD_TIME: u32 = 1622; // 2.5ms
pub const TSADCV5_AUTO_PERIOD_HT_TIME: u32 = 1622; // 2.5ms
pub const TSADCV6_AUTO_PERIOD_TIME: u32 = 5000; // 2.5ms
pub const TSADCV6_AUTO_PERIOD_HT_TIME: u32 = 5000; // 2.5ms

// SOC-specific constants
pub const TSADCV2_USER_INTER_PD_SOC: u32 = 0x340; // 13 clocks
pub const TSADCV5_USER_INTER_PD_SOC: u32 = 0xfc0; // 97us, at least 90us

// GRF register addresses
pub const GRF_ADDR: u32 = 0xff77e000;
pub const GRF_SARADC_TESTBIT: u32 = 0x0e644;
pub const GRF_TSADC_TESTBIT_L: u32 = 0x0e648;
pub const GRF_TSADC_TESTBIT_H: u32 = 0x0e64c;

pub const GRF_SARADC_TESTBIT_ON: u32 = 0x10001 << 2;
pub const GRF_TSADC_TESTBIT_H_ON: u32 = 0x10001 << 2;
pub const GRF_TSADC_VCM_EN_L: u32 = 0x10001 << 7;
pub const GRF_TSADC_VCM_EN_H: u32 = 0x10001 << 7;
pub const GRF_CON_TSADC_CH_INV: u32 = 0x10001 << 1;
