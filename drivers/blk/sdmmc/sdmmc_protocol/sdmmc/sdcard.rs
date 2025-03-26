use core::fmt::{self, Write};

use sel4_microkit_support::debug_log;

use super::{
    mmc_struct::{self, BlockTransmissionMode, MmcBusWidth, MmcState},
    sdmmc_capability::SdcardCapability,
    SdmmcError, SdmmcHardware, SdmmcProtocol,
};

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
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SdVersion {
    V1_0 = 1,
    V2_0 = 2,
    V3_0 = 3,
    V4_0 = 4,
}

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
        let cid_combined = ((cid[0] as u128) << 96)
            | ((cid[1] as u128) << 64)
            | ((cid[2] as u128) << 32)
            | (cid[3] as u128);

        // Extract each field based on the CID structure
        let manufacturer_id = ((cid_combined >> 120) & 0xFF) as u8;
        let oem_id = ((cid_combined >> 104) & 0xFFFF) as u16;

        // Extract product name, which is 5 bytes (40 bits)
        let product_name = [
            ((cid_combined >> 96) & 0xFF) as u8,
            ((cid_combined >> 88) & 0xFF) as u8,
            ((cid_combined >> 80) & 0xFF) as u8,
            ((cid_combined >> 72) & 0xFF) as u8,
            ((cid_combined >> 64) & 0xFF) as u8,
        ];

        let product_revision = ((cid_combined >> 56) & 0xFF) as u8;
        let serial_number = ((cid_combined >> 24) & 0xFFFFFFFF) as u32;

        // Extract year and month from the manufacturing date
        let year = ((cid_combined >> 12) & 0x0F) as u32 + 2000;
        let month = ((cid_combined >> 8) & 0x0F) as u8;

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

trait ToArray {
    fn to_array(&self) -> [u8; 128]; // A fixed buffer size that you can change as needed
}

impl ToArray for Cid {
    fn to_array(&self) -> [u8; 128] {
        let mut buf = [0u8; 128];
        let mut writer = ArrayWriter::new(&mut buf);

        write!(
            writer,
            "Manufacturer ID: {}\nOEM ID: {}\nProduct Name: {}\nProduct Revision: {}\n\
            Serial Number: {}\nManufacturing Date: {}-{}\n",
            self.manufacturer_id,
            self.oem_id,
            core::str::from_utf8(&self.product_name).unwrap_or("?????"),
            self.product_revision,
            self.serial_number,
            self.manufacturing_date.0,
            self.manufacturing_date.1,
        )
        .ok();

        buf
    }
}

// This struct is super unreliable, I am thinking
pub(crate) struct Csd {
    csd_structure: u8,
    card_capacity: u64,
    max_read_block_len: u16,
    max_write_block_len: u16,
    erase_sector_size: u32,
    supports_partial_write: bool,
}

impl Csd {
    pub fn new(csd: [u32; 4]) -> (Csd, SdVersion) {
        // Combine the four 32-bit words into a single 128-bit value for easier bit manipulation
        let csd_combined = ((csd[0] as u128) << 96)
            | ((csd[1] as u128) << 64)
            | ((csd[2] as u128) << 32)
            | (csd[3] as u128);

        // Extract the CSD structure version
        let csd_structure = ((csd_combined >> 126) & 0x3) as u8; // Bits 126–127
        let sd_version = match csd_structure {
            0 => SdVersion::V1_0, // CSD Version 1.0
            1 => SdVersion::V2_0, // CSD Version 2.0
            // Even if the parsing csd fails, it should not crash the driver completely
            _ => panic!("Unsupported CSD structure version"), // CSD structures beyond 2.0 are not supported here
                                                              // Actually SDUC card are using CSD 3.0 so maybe add something here later.
        };

        // Parse fields based on CSD version
        let (card_capacity, erase_sector_size) = match sd_version {
            SdVersion::V1_0 => {
                // CSD Version 1.0 capacity calculation
                let c_size = ((csd_combined >> 62) & 0xFFF) as u64; // Bits 62–73
                let c_size_mult = ((csd_combined >> 47) & 0x7) as u64; // Bits 47–49
                let read_bl_len = ((csd_combined >> 80) & 0xF) as u64; // Bits 80–83
                let card_capacity = (c_size + 1) * (1 << (c_size_mult + 2)) * (1 << read_bl_len);

                // Erase sector size is calculated differently in CSD Version 1.0
                let sector_size = ((csd_combined >> 39) & 0x7F) as u32 + 1; // Bits 39–45
                (card_capacity, sector_size)
            }
            SdVersion::V2_0 => {
                // CSD Version 2.0 capacity calculation for SDHC/SDXC
                let c_size = ((csd_combined >> 48) & 0x3FFFF) as u64; // Bits 48–69
                let card_capacity = (c_size + 1) * 512 * 1024; // Capacity formula for SDHC/SDXC

                // Erase sector size calculation for CSD Version 2.0
                let sector_size = ((csd_combined >> 39) & 0x7F + 1) as u32 * 512; // Bits 39–45

                (card_capacity, sector_size)
            }
            SdVersion::V3_0 => unreachable!(),
            SdVersion::V4_0 => unreachable!(),
        };

        // Block lengths (same for both versions)
        let read_bl_len = ((csd_combined >> 80) & 0xF) as u16; // Bits 80–83
        let max_read_block_len = 1 << read_bl_len;

        let write_bl_len = ((csd_combined >> 22) & 0xF) as u16; // Bits 22–25
        let max_write_block_len = 1 << write_bl_len;

        // Partial write support (same for both versions)
        let supports_partial_write = ((csd_combined >> 21) & 0x1) != 0; // Bit 21

        // Return the constructed CSD struct along with the SD version
        (
            Csd {
                csd_structure,
                card_capacity,
                max_read_block_len,
                max_write_block_len,
                erase_sector_size,
                supports_partial_write,
            },
            sd_version,
        )
    }
}

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

        debug_log!("Supported cmd: {:?}\n", supported_cmd);

        let mut data_stat_after_erase: bool = false;
        if scr_raw & (0b1 << 55) != 0 {
            data_stat_after_erase = true;
        }
        debug_log!("Data status after erase: {:?}\n", data_stat_after_erase);

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

struct ArrayWriter<'a> {
    buf: &'a mut [u8],
    pos: usize,
}

impl<'a> ArrayWriter<'a> {
    fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, pos: 0 }
    }
}

impl<'a> Write for ArrayWriter<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let bytes = s.as_bytes();
        let len = bytes.len();

        if self.pos + len > self.buf.len() {
            return Err(fmt::Error);
        }

        self.buf[self.pos..self.pos + len].copy_from_slice(bytes);

        self.pos += len;
        Ok(())
    }
}

/*
/// Parses the R1 response from an SD card command.
/// The function takes a 32-bit unsigned integer representing the R1 response
/// and returns a structured report of the status.
///
/// # Arguments
/// * `response` - The 32-bit R1 response from the SD card command.
///
/// # Returns
/// A result with either Ok (no errors) or an error string describing the problem.
fn parse_r1_response(response: u32) -> Result<String, String> {
    // Check each status bit and gather relevant info.
    let out_of_range = (response >> 31) & 1 != 0;
    let address_error = (response >> 30) & 1 != 0;
    let block_len_error = (response >> 29) & 1 != 0;
    let erase_seq_error = (response >> 28) & 1 != 0;
    let ready_for_data = (response >> 8) & 1 != 0;
    let idle_state = (response >> 0) & 1 != 0;

    // Extract card state (bits 9-12).
    let card_state = (response >> 9) & 0xF;

    // Collect error messages for any issues found.
    let mut errors = Vec::new();
    if out_of_range { errors.push("Out of range error"); }
    if address_error { errors.push("Address error"); }
    if block_len_error { errors.push("Block length error"); }
    if erase_seq_error { errors.push("Erase sequence error"); }

    // Parse and interpret card state
    let state_description = match card_state {
        0 => "Idle",
        1 => "Ready",
        2 => "Identification",
        3 => "Standby",
        4 => "Transfer",
        5 => "Sending Data",
        6 => "Receive Data",
        7 => "Programming",
        8 => "Disconnect",
        _ => "Unknown",
    };

    // Report ready status or errors.
    if !errors.is_empty() {
        Err(format!("R1 response contains errors: {}", errors.join(", ")))
    } else if !ready_for_data {
        Err("Card is not ready for data.".to_string())
    } else {
        Ok(format!("R1 response is valid. Card state: {}", state_description))
    }
}
*/
