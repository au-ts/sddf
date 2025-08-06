use bitflags::bitflags;

// Linux protocol layer use two u32 to represent all capabilities
// In this Rust based protocol layer we use u128.
// I have thought about whether I should seperate the SdmmcHostCapability to two structs, one for sdcard, one for eMMC
// But give up this idea because I do not know if there are such host that support both sdcard and eMMC
pub(crate) struct SdmmcHostCapability(pub u128);

bitflags! {
    /// Represents the host capabilities for SD/MMC controllers
    impl SdmmcHostCapability: u128 {
        // Timing modes
        const MMC_TIMING_LEGACY       = MMC_TIMING_LEGACY;
        const MMC_TIMING_MMC_HS       = MMC_TIMING_MMC_HS;
        const MMC_TIMING_SD_HS        = MMC_TIMING_SD_HS;
        const MMC_TIMING_UHS_SDR12    = MMC_TIMING_UHS_SDR12;
        const MMC_TIMING_UHS_SDR25    = MMC_TIMING_UHS_SDR25;
        const MMC_TIMING_UHS_SDR50    = MMC_TIMING_UHS_SDR50;
        const MMC_TIMING_UHS_SDR104   = MMC_TIMING_UHS_SDR104;
        const MMC_TIMING_UHS_DDR50    = MMC_TIMING_UHS_DDR50;
        const MMC_TIMING_MMC_DDR52    = MMC_TIMING_MMC_DDR52;
        const MMC_TIMING_MMC_HS200    = MMC_TIMING_MMC_HS200;
        const MMC_TIMING_MMC_HS400    = MMC_TIMING_MMC_HS400;
        const MMC_TIMING_SD_EXP       = MMC_TIMING_SD_EXP;
        const MMC_TIMING_SD_EXP_1_2V  = MMC_TIMING_SD_EXP_1_2V;

        // Capabilities
        const MMC_CAP_4_BIT_DATA      = MMC_CAP_4_BIT_DATA;
        const MMC_CAP_8_BIT_DATA      = MMC_CAP_8_BIT_DATA;
        const MMC_CAP_BUS_WIDTH_TEST  = MMC_CAP_BUS_WIDTH_TEST;

        const MMC_CAP_AUTO_STOP       = MMC_CAP_AUTO_STOP;
    }
}
#[derive(Debug, Clone)]
pub(crate) struct SdcardCapability(pub u128);

bitflags! {
    /// Represents the host capabilities for SD/MMC controllers
    impl SdcardCapability: u128 {
        // Timing modes
        const MMC_TIMING_LEGACY       = MMC_TIMING_LEGACY;
        const MMC_TIMING_MMC_HS       = MMC_TIMING_MMC_HS;
        const MMC_TIMING_SD_HS        = MMC_TIMING_SD_HS;
        const MMC_TIMING_UHS_SDR12    = MMC_TIMING_UHS_SDR12;
        const MMC_TIMING_UHS_SDR25    = MMC_TIMING_UHS_SDR25;
        const MMC_TIMING_UHS_SDR50    = MMC_TIMING_UHS_SDR50;
        const MMC_TIMING_UHS_SDR104   = MMC_TIMING_UHS_SDR104;
        const MMC_TIMING_UHS_DDR50    = MMC_TIMING_UHS_DDR50;
        const MMC_TIMING_SD_EXP       = MMC_TIMING_SD_EXP;
        const MMC_TIMING_SD_EXP_1_2V  = MMC_TIMING_SD_EXP_1_2V;

        // Capabilities
        const MMC_CAP_4_BIT_DATA      = MMC_CAP_4_BIT_DATA;

        const MMC_CAP_CMD23           = MMC_CAP_CMD23;
        const MMC_CAP_AUTO_STOP       = MMC_CAP_AUTO_STOP;
    }
}

pub const MMC_EMPTY_CAP: u128 = 0;

// Timing modes (starting from bit 0)
pub const MMC_TIMING_LEGACY: u128 = 1 << 0;
pub const MMC_TIMING_MMC_HS: u128 = 1 << 1;
pub const MMC_TIMING_SD_HS: u128 = 1 << 2;
pub const MMC_TIMING_UHS_SDR12: u128 = 1 << 3;
pub const MMC_TIMING_UHS_SDR25: u128 = 1 << 4;
pub const MMC_TIMING_UHS_SDR50: u128 = 1 << 5;
pub const MMC_TIMING_UHS_DDR50: u128 = 1 << 6;
pub const MMC_TIMING_UHS_SDR104: u128 = 1 << 7;
pub const MMC_TIMING_MMC_DDR52: u128 = 1 << 8;
pub const MMC_TIMING_MMC_HS200: u128 = 1 << 9;
pub const MMC_TIMING_MMC_HS400: u128 = 1 << 10;

pub const MMC_TIMING_UHS: u128 = MMC_TIMING_UHS_SDR12
    | MMC_TIMING_UHS_SDR25
    | MMC_TIMING_UHS_SDR50
    | MMC_TIMING_UHS_SDR104
    | MMC_TIMING_UHS_DDR50;

pub const MMC_TIMING_SD_EXP: u128 = 1 << 11;
pub const MMC_TIMING_SD_EXP_1_2V: u128 = 1 << 12;

// Capabilities
pub const MMC_CAP_4_BIT_DATA: u128 = 1 << 16;
pub const MMC_CAP_8_BIT_DATA: u128 = 1 << 17;

pub const MMC_CAP_BUS_WIDTH_TEST: u128 = 1 << 18;

pub const MMC_CAP_CMD23: u128 = 1 << 30;
pub const MMC_CAP_AUTO_STOP: u128 = 1 << 31;

// Host VDD voltage levels for MMC/SD card
pub const MMC_VDD_165_195: u32 = 0x0000_0080; // VDD voltage 1.65 - 1.95V
pub const MMC_VDD_20_21: u32 = 0x0000_0100; // VDD voltage 2.0 - 2.1V
pub const MMC_VDD_21_22: u32 = 0x0000_0200; // VDD voltage 2.1 - 2.2V
pub const MMC_VDD_22_23: u32 = 0x0000_0400; // VDD voltage 2.2 - 2.3V
pub const MMC_VDD_23_24: u32 = 0x0000_0800; // VDD voltage 2.3 - 2.4V
pub const MMC_VDD_24_25: u32 = 0x0000_1000; // VDD voltage 2.4 - 2.5V
pub const MMC_VDD_25_26: u32 = 0x0000_2000; // VDD voltage 2.5 - 2.6V
pub const MMC_VDD_26_27: u32 = 0x0000_4000; // VDD voltage 2.6 - 2.7V
pub const MMC_VDD_27_28: u32 = 0x0000_8000; // VDD voltage 2.7 - 2.8V
pub const MMC_VDD_28_29: u32 = 0x0001_0000; // VDD voltage 2.8 - 2.9V
pub const MMC_VDD_29_30: u32 = 0x0002_0000; // VDD voltage 2.9 - 3.0V
pub const MMC_VDD_30_31: u32 = 0x0004_0000; // VDD voltage 3.0 - 3.1V
pub const MMC_VDD_31_32: u32 = 0x0008_0000; // VDD voltage 3.1 - 3.2V
pub const MMC_VDD_32_33: u32 = 0x0010_0000; // VDD voltage 3.2 - 3.3V
pub const MMC_VDD_33_34: u32 = 0x0020_0000; // VDD voltage 3.3 - 3.4V
pub const MMC_VDD_34_35: u32 = 0x0040_0000; // VDD voltage 3.4 - 3.5V
pub const MMC_VDD_35_36: u32 = 0x0080_0000; // VDD voltage 3.5 - 3.6V
