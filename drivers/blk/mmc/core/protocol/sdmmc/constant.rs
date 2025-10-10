// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

#![allow(dead_code)] // Allow dead code for the entire module

// Define constants for MMC data flags
pub const MMC_DATA_READ: u32 = 1;
pub const MMC_DATA_WRITE: u32 = 2;

// Define constants for MMC commands
pub const MMC_CMD_GO_IDLE_STATE: u32 = 0;
pub const MMC_CMD_SEND_OP_COND: u32 = 1;
pub const MMC_CMD_ALL_SEND_CID: u32 = 2;
pub const MMC_CMD_SET_RELATIVE_ADDR: u32 = 3;
pub const MMC_CMD_SET_DSR: u32 = 4;
pub const MMC_CMD_SWITCH: u32 = 6;
pub const MMC_CMD_SELECT_CARD: u32 = 7;
pub const MMC_CMD_SEND_EXT_CSD: u32 = 8;
pub const MMC_CMD_SEND_CSD: u32 = 9;
pub const MMC_CMD_SEND_CID: u32 = 10;
pub const MMC_CMD_STOP_TRANSMISSION: u32 = 12;
pub const MMC_CMD_SEND_STATUS: u32 = 13;
pub const MMC_CMD_SET_BLOCKLEN: u32 = 16;
pub const MMC_CMD_READ_SINGLE_BLOCK: u32 = 17;
pub const MMC_CMD_READ_MULTIPLE_BLOCK: u32 = 18;
pub const MMC_CMD_SEND_TUNING_BLOCK: u32 = 19;
pub const MMC_CMD_SEND_TUNING_BLOCK_HS200: u32 = 21;
pub const MMC_CMD_SET_BLOCK_COUNT: u32 = 23;
pub const MMC_CMD_WRITE_SINGLE_BLOCK: u32 = 24;
pub const MMC_CMD_WRITE_MULTIPLE_BLOCK: u32 = 25;
pub const MMC_CMD_ERASE_GROUP_START: u32 = 35;
pub const MMC_CMD_ERASE_GROUP_END: u32 = 36;
pub const MMC_CMD_ERASE: u32 = 38;
pub const MMC_CMD_APP_CMD: u32 = 55;
pub const MMC_CMD_SPI_READ_OCR: u32 = 58;
pub const MMC_CMD_SPI_CRC_ON_OFF: u32 = 59;
pub const MMC_CMD_RES_MAN: u32 = 62;

// Define constants for MMC command 62 arguments
pub const MMC_CMD62_ARG1: u32 = 0xefac62ec;
pub const MMC_CMD62_ARG2: u32 = 0xcbaea7;

// Define constants for SD commands
pub const SD_CMD_SEND_RELATIVE_ADDR: u32 = 3;
pub const SD_CMD_SWITCH_FUNC: u32 = 6;
pub const SD_CMD_SEND_IF_COND: u32 = 8;
pub const SD_CMD_SWITCH_UHS18V: u32 = 11;

pub const SD_CMD_APP_SET_BUS_WIDTH: u32 = 6;
pub const SD_CMD_APP_SD_STATUS: u32 = 13;

pub const SD_CMD_ERASE_WR_BLK_START: u32 = 32;
pub const SD_CMD_ERASE_WR_BLK_END: u32 = 33;

/*
 * Erase/discard
 */
pub const SD_ERASE_ARG: u32 = 0x00000000;
pub const SD_DISCARD_ARG: u32 = 0x00000001;

pub const SD_CMD_APP_SEND_OP_COND: u32 = 41;
pub const SD_CMD_APP_SEND_SCR: u32 = 51;

pub const OCR_BUSY: u32 = 0x8000_0000;
pub const OCR_XPC: u32 = 0x1000_0000;
pub const OCR_HCS: u32 = 0x4000_0000;
pub const OCR_S18R: u32 = 0x0100_0000;
pub const OCR_VOLTAGE_MASK: u32 = 0x007F_FF80;
pub const OCR_ACCESS_MODE: u32 = 0x6000_0000;

// The index to get the speed class information from SD switch function cmd
// Check Part 1 Physical Layer Simplified Specification Ver9.10 table 4-11 to see if I am wrong
pub const SD_SWITCH_FUNCTION_GROUP_ONE: usize = 13;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_SET_LEGACY: u8 = 0x0;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_SET_SDHS: u8 = 0x1;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR12: u8 = 0x0;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR25: u8 = 0x1;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR50: u8 = 0x2;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR104: u8 = 0x3;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_DDR50: u8 = 0x4;

pub const SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_LEGACY: u8 =
    1 << SD_SWITCH_FUNCTION_GROUP_ONE_SET_LEGACY;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_SDHS: u8 = 1 << SD_SWITCH_FUNCTION_GROUP_ONE_SET_SDHS;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR12: u8 =
    1 << SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR12;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR25: u8 =
    1 << SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR25;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR50: u8 =
    1 << SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR50;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR104: u8 =
    1 << SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR104;
pub const SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_DDR50: u8 =
    1 << SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_DDR50;

pub const SD_SWITCH_FUNCTION_SELECTION_GROUP_ONE: usize = 16;
