// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

use core::sync::atomic::Ordering;

use crate::{
    dev_log, info,
    sdmmc::{
        MMC_RSP_R1, MmcData, MmcDataFlag, SdmmcCmd,
        constant::{MMC_CMD_APP_CMD, SD_CMD_APP_SEND_SCR, SD_CMD_SWITCH_FUNC},
        mmc_struct::CardInfo,
    },
    sdmmc_os::Sleep,
    sdmmc_traits::SdmmcHardware,
};

use super::{
    SdmmcError,
    capability::SdcardCapability,
    mmc_struct::{BlockTransmissionMode, MmcBusWidth, MmcState},
};

#[allow(dead_code)]
pub struct Sdcard {
    pub(crate) card_id: u128,
    pub(crate) manufacture_info: Cid,
    pub(crate) card_specific_data: Csd,
    pub(crate) card_version: SdVersion,
    pub(crate) relative_card_addr: u16,
    pub(crate) card_state: MmcState,
    pub(crate) card_cap: SdcardCapability,
    pub(crate) method: BlockTransmissionMode,
    pub(crate) card_config: Option<Scr>,
}

impl Sdcard {
    /// Unsafe because dereference raw pointer
    pub(crate) unsafe fn sdcard_get_configuration_register<T: SdmmcHardware>(
        hardware: &mut T,
        sleep: &mut dyn Sleep,
        physical_memory: u64,
        raw_memory: *mut [u8; 64],
        invalidate_cache_fn: fn(),
        rca: u16,
    ) -> Result<Scr, SdmmcError> {
        let mut resp: [u32; 4] = [0; 4];
        let mut cmd: SdmmcCmd = SdmmcCmd {
            cmdidx: MMC_CMD_APP_CMD,
            resp_type: MMC_RSP_R1,
            cmdarg: (rca as u32) << 16,
        };
        hardware.sdmmc_do_request(sleep, &cmd, None, &mut resp, 0)?;

        cmd = SdmmcCmd {
            cmdidx: SD_CMD_APP_SEND_SCR,
            resp_type: MMC_RSP_R1,
            cmdarg: 0,
        };
        let data: MmcData = MmcData {
            blocksize: 8,
            blockcnt: 1,
            flags: MmcDataFlag::SdmmcDataRead,
            addr: physical_memory,
        };

        hardware.sdmmc_do_request(sleep, &cmd, Some(&data), &mut resp, 0)?;

        core::sync::atomic::fence(Ordering::Acquire);

        invalidate_cache_fn();

        // print out the content of the SCR register
        crate::dev_log!("SCR register content: ");
        unsafe { crate::sdmmc::print_one_block(raw_memory as *const u8, 8) };

        // The sdcard register data is always in big endian format
        // Now we construct the last 32 bits of the scr register
        let scr_raw: u64 = unsafe {
            ((((*raw_memory)[0] as u64) << 24)
                + (((*raw_memory)[1] as u64) << 16)
                + (((*raw_memory)[2] as u64) << 8)
                + ((*raw_memory)[3] as u64))
                << 32
        };

        let scr: Scr = Scr::new(scr_raw)?;

        Ok(scr)
    }

    pub fn sdcard_test_tuning<T: SdmmcHardware>(
        hardware: &mut T,
        sleep: &mut dyn Sleep,
        memory: *mut [u8; 64],
    ) -> Result<(), SdmmcError> {
        let mut resp: [u32; 4] = [0; 4];

        let data = MmcData {
            blocksize: 64,
            blockcnt: 1,
            flags: MmcDataFlag::SdmmcDataRead,
            addr: memory as u64,
        };

        let cmd = SdmmcCmd {
            cmdidx: SD_CMD_SWITCH_FUNC,
            resp_type: MMC_RSP_R1,
            cmdarg: 0x00FFFFFF,
        };

        hardware.sdmmc_do_request(sleep, &cmd, Some(&data), &mut resp, 1)
    }

    pub fn print_info(&self) {
        const LABEL_WIDTH: usize = 20;
        const DATA_WIDTH: usize = 25;
        let capacity_bytes = self.card_specific_data.card_capacity;

        const KB: u64 = 1024;
        const MB: u64 = 1024 * KB;
        const GB: u64 = 1024 * MB;
        const TB: u64 = 1024 * GB;

        info!("\n\n╔═════════════════════════════════════════════════╗");
        info!("║ SDCARD INFORMATION                              ║");
        info!("╠═════════════════════════════════════════════════╣");
        info!(
            "║ {:<label_width$}: {:<data_width$} ║", // Pad the value side as well
            "Manufacturer ID",
            self.manufacture_info.manufacturer_id,
            label_width = LABEL_WIDTH,
            data_width = DATA_WIDTH,
        );
        info!(
            "║ {:<label_width$}: {:<data_width$} ║",
            "OEM ID",
            self.manufacture_info.oem_id,
            label_width = LABEL_WIDTH,
            data_width = DATA_WIDTH,
        );
        info!(
            "║ {:<label_width$}: {:<data_width$} ║",
            "Product Name",
            core::str::from_utf8(&self.manufacture_info.product_name).unwrap_or("?????"),
            label_width = LABEL_WIDTH,
            data_width = DATA_WIDTH,
        );
        info!(
            "║ {:<label_width$}: {:<data_width$} ║",
            "Product Revision",
            self.manufacture_info.product_revision,
            label_width = LABEL_WIDTH,
            data_width = DATA_WIDTH,
        );
        info!(
            "║ {:<label_width$}: {:<data_width$} ║",
            "Serial Number",
            self.manufacture_info.serial_number,
            label_width = LABEL_WIDTH,
            data_width = DATA_WIDTH,
        );
        info!(
            "║ {:<label_width$}: {:<data_width$}{:padding$} ║",
            "Manufacturing Date",
            &format_args!(
                "{:4}-{:02}",
                self.manufacture_info.manufacturing_date.0,
                self.manufacture_info.manufacturing_date.1
            ),
            "",
            label_width = LABEL_WIDTH,
            data_width = DATA_WIDTH,
            padding = DATA_WIDTH - 7
        );

        let (val, fraction, unit) = match capacity_bytes {
            c if c >= TB => (c / TB, (c % TB) / GB, "TB"),
            c if c >= GB => (c / GB, (c % GB) / MB, "GB"),
            c if c >= MB => (c / MB, (c % MB) / KB, "MB"),
            c if c >= KB => (c / KB, c % KB, "KB"),
            c => (c, 0, "Bytes"),
        };
        if fraction == 0 {
            info!(
                "║ {:<label_width$}: {:<data_width$} ║",
                "Card Capacity",
                &format_args!(
                    "{} {}{:padding$}",
                    val,
                    unit,
                    "",
                    padding = DATA_WIDTH - 4 - val.ilog10() as usize
                ),
                label_width = LABEL_WIDTH,
                data_width = DATA_WIDTH
            );
        } else {
            info!(
                "║ {:<label_width$}: {}{:padding$} ║",
                "Card Capacity",
                &format_args!("{}.{:0<3} {}", val, (fraction * 1000) / 1024, unit),
                "",
                label_width = LABEL_WIDTH,
                padding = DATA_WIDTH - val.ilog10() as usize - 8
            );
        }

        info!("╚═════════════════════════════════════════════════╝\n");
    }

    pub fn sdcard_info(&self) -> CardInfo {
        CardInfo {
            card_id: self.card_id,
            card_capacity: self.card_specific_data.card_capacity,
            card_state: self.card_state.clone(),
        }
    }
}

/// Placeholder eMMC struct that is not implemented
pub struct EMmc {
    pub card_id: u128,
    pub method: BlockTransmissionMode,
}

// Beware this struct is meant to track the cmd set that the sdcard should support
// For example, if the SdVersion is set to V3_0, it does not mean the card version is 3.0
// But mean that the sdcard support cmd at least up to specification 3.0
// The SD card specification is cumulative, meaning that if an SD card reports support for a
// particular version (say 4.0), it implicitly supports all earlier versions as well.
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SdVersion {
    V1_0 = 1,
    V2_0 = 2,
    V3_0 = 3,
    V4_0 = 4,
}

#[derive(Debug)]
pub(crate) struct Cid {
    manufacturer_id: u8,
    oem_id: u16,
    product_name: [u8; 5],
    product_revision: u8,
    serial_number: u32,
    manufacturing_date: (u32, u8), // (year, month)
}

impl Cid {
    pub fn new(cid: [u32; 4]) -> Cid {
        // Combine the 4 u32 words into a single 128-bit CID value for easy bit manipulation
        let cid_combined: u128 = ((cid[0] as u128) << 96)
            | ((cid[1] as u128) << 64)
            | ((cid[2] as u128) << 32)
            | (cid[3] as u128);

        // Extract each field based on the CID structure
        let manufacturer_id = ((cid_combined >> 120) & 0xFF) as u8;
        let oem_id = ((cid_combined >> 104) & 0xFFFF) as u16;

        // Extract product name, which is 5 bytes (40 bits)
        let product_name: [u8; 5] = [
            ((cid_combined >> 96) & 0xFF) as u8,
            ((cid_combined >> 88) & 0xFF) as u8,
            ((cid_combined >> 80) & 0xFF) as u8,
            ((cid_combined >> 72) & 0xFF) as u8,
            ((cid_combined >> 64) & 0xFF) as u8,
        ];

        let product_revision: u8 = ((cid_combined >> 56) & 0xFF) as u8;
        let serial_number: u32 = ((cid_combined >> 24) & 0xFFFFFFFF) as u32;

        // Extract year and month from the manufacturing date
        let year: u32 = ((cid_combined >> 12) & 0xFF) as u32 + 2000;
        let month: u8 = ((cid_combined >> 8) & 0x0F) as u8;

        Cid {
            manufacturer_id,
            oem_id,
            product_name,
            product_revision,
            serial_number,
            manufacturing_date: (year, month),
        }
    }
}

// This struct is super unreliable, I am thinking
#[allow(dead_code)]
#[derive(Debug)]
pub(crate) struct Csd {
    csd_structure: u8,
    card_capacity: u64,
    max_read_block_len: u16,
    max_write_block_len: u16,
    erase_sector_size: u32,
    supports_partial_write: bool,
}

impl Csd {
    pub fn new(csd: [u32; 4]) -> Result<(Csd, SdVersion), SdmmcError> {
        // Combine the four 32-bit words into a single 128-bit value for easier bit manipulation
        let csd_combined: u128 = ((csd[0] as u128) << 96)
            | ((csd[1] as u128) << 64)
            | ((csd[2] as u128) << 32)
            | (csd[3] as u128);

        // Extract the CSD structure version
        let csd_structure: u8 = ((csd_combined >> 126) & 0x3) as u8; // Bits 126–127
        let sd_version: SdVersion = match csd_structure {
            0 => SdVersion::V1_0, // CSD Version 1.0
            1 => SdVersion::V2_0, // CSD Version 2.0
            // Even if the parsing csd fails, it should not crash the driver completely
            _ => return Err(SdmmcError::EUNSUPPORTEDCARD), // CSD structures beyond 2.0 are not supported here
                                                           // Actually SDUC card are using CSD 3.0 so maybe add something here later.
        };

        // Parse fields based on CSD version
        let (card_capacity, erase_sector_size) = match sd_version {
            SdVersion::V1_0 => {
                // CSD Version 1.0 capacity calculation
                let c_size: u64 = ((csd_combined >> 62) & 0xFFF) as u64; // Bits 62–73
                let c_size_mult: u64 = ((csd_combined >> 47) & 0x7) as u64; // Bits 47–49
                let read_bl_len: u64 = ((csd_combined >> 80) & 0xF) as u64; // Bits 80–83
                let card_capacity: u64 =
                    (c_size + 1) * (1 << (c_size_mult + 2)) * (1 << read_bl_len);

                // Erase sector size is calculated differently in CSD Version 1.0
                let sector_size: u32 = ((csd_combined >> 39) & 0x7F) as u32 + 1; // Bits 39–45
                (card_capacity, sector_size)
            }
            SdVersion::V2_0 => {
                // CSD Version 2.0 capacity calculation for SDHC/SDXC
                let c_size: u64 = ((csd_combined >> 48) & 0x3FFFFF) as u64; // Bits 48–69
                let card_capacity: u64 = (c_size + 1) * 512 * 1024; // Capacity formula for SDHC/SDXC

                // Erase sector size calculation for CSD Version 2.0
                let sector_size: u32 = ((csd_combined >> 39) & 0x7F + 1) as u32 * 512; // Bits 39–45

                (card_capacity, sector_size)
            }
            SdVersion::V3_0 => return Err(SdmmcError::EINVAL),
            SdVersion::V4_0 => return Err(SdmmcError::EINVAL),
        };

        // Block lengths (same for both versions)
        let read_bl_len: u16 = ((csd_combined >> 80) & 0xF) as u16; // Bits 80–83
        let max_read_block_len: u16 = 1 << read_bl_len;

        let write_bl_len: u16 = ((csd_combined >> 22) & 0xF) as u16; // Bits 22–25
        let max_write_block_len: u16 = 1 << write_bl_len;

        // Partial write support (same for both versions)
        let supports_partial_write: bool = ((csd_combined >> 21) & 0x1) != 0; // Bit 21

        // Return the constructed CSD struct along with the SD version
        Ok((
            Csd {
                csd_structure,
                card_capacity,
                max_read_block_len,
                max_write_block_len,
                erase_sector_size,
                supports_partial_write,
            },
            sd_version,
        ))
    }
}

#[allow(dead_code)]
#[derive(Debug)]
pub(crate) struct Scr {
    // Not extracted from Scr parsing yet
    pub sd_spec: u32,
    pub data_stat_after_erase: bool,
    // Not extracted from Scr parsing yet
    sd_security: u8,
    pub sd_bus_width: MmcBusWidth,
    pub support_speed_class_control: bool,
    pub support_set_block_count: bool,
    pub support_extersion_register_single_block: bool,
    pub support_extersion_register_multi_block: bool,
    pub support_security_transmission: bool,
}

impl Scr {
    // Input variable: raw scr data
    pub fn new(scr_raw: u64) -> Result<Scr, SdmmcError> {
        if scr_raw & (0b1 << 48) != (0b1 << 48) {
            return Err(SdmmcError::EINVAL);
        }

        let mut sd_bus_width: MmcBusWidth = MmcBusWidth::Width1;

        if scr_raw & (0b1 << 50) == (0b1 << 50) {
            sd_bus_width = MmcBusWidth::Width4;
        }

        // Extract bits 32-36 as a single value (5 bits = 0-31 range)
        // Shift right 32 bits and mask with 0b11111 (31)
        let command_support_bits = (scr_raw >> 32) & 0b11111;

        // Convert to bool array
        let mut supported_cmd: [bool; 5] = [false; 5];
        for i in 0..5 {
            supported_cmd[i] = (command_support_bits & (1 << i)) != 0;
        }

        dev_log!("Supported cmd: {:?}\n", supported_cmd);

        let mut data_stat_after_erase: bool = false;
        if scr_raw & (0b1 << 55) != 0 {
            data_stat_after_erase = true;
        }
        dev_log!("Data status after erase: {:?}\n", data_stat_after_erase);

        Ok(Scr {
            sd_spec: 0,
            data_stat_after_erase,
            sd_security: 0,
            sd_bus_width,
            support_speed_class_control: supported_cmd[0],
            support_set_block_count: supported_cmd[1],
            support_extersion_register_single_block: supported_cmd[2],
            support_extersion_register_multi_block: supported_cmd[3],
            support_security_transmission: supported_cmd[4],
        })
    }
}
