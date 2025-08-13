// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

use super::sd::{EMmc, Sdcard};

// Enums for bus_width
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MmcBusWidth {
    Width1 = 0,
    // One is skipped because for SD_ACMD_SET_BUS_WIDTH, setting cmdargs to 2 indicate 4 datalanes
    Width4 = 2,
    Width8 = 3,
}

// Timing modes (could be an enum or use the bitflags constants defined earlier)
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum MmcTiming {
    Legacy = 0,
    MmcHs = 1,
    SdHs = 2,
    UhsSdr12 = 3,
    UhsSdr25 = 4,
    UhsSdr50 = 5,
    UhsSdr104 = 6,
    UhsDdr50 = 7,
    MmcDdr52 = 8,
    MmcHs200 = 9,
    MmcHs400 = 10,
    SdExp = 11,
    SdExp12V = 12,
    CardSetup = 13, // Additional frequency for card setup
    CardSleep = 14,
    ClockStop = 15,
}

#[derive(Debug, Clone)]
pub struct MmcState {
    /// The timing specification that dictates how data is transferred between the host
    /// and the card.
    ///
    /// - The timing mode defines the protocol and speed class for communication, such as
    ///   legacy modes, high-speed modes, or ultra-high-speed modes.
    /// - Examples include:
    ///   - `Timing::Legacy`: Legacy slower transfer mode.
    ///   - `Timing::SdHs`: SD high-speed mode.
    ///   - `Timing::MmcHs200`: eMMC HS200 mode for high-speed data transfers.
    pub timing: MmcTiming,

    /// The width of the data bus used for communication between the host and the card.
    ///
    /// - This field specifies whether the bus operates in 1-bit, 4-bit, or 8-bit mode.
    /// - Wider bus widths (4-bit, 8-bit) enable higher data transfer rates, but not all
    ///   cards or host controllers support every bus width.
    /// - Common values:
    ///   - `BusWidth::Width1`: 1-bit data width (lowest speed, used during initialization).
    ///   - `BusWidth::Width4`: 4-bit data width (common for SD cards).
    ///   - `BusWidth::Width8`: 8-bit data width (mainly for eMMC).
    pub bus_width: MmcBusWidth,
}

/// Some of the MmcDevice is reserved for future use
#[allow(dead_code)]
pub(crate) enum MmcDevice {
    Sdcard(Sdcard),
    EMmc(EMmc),
    Unknown,
}

/// Represents the different states of an SD or eMMC card.
/// Not used yet
#[allow(dead_code)]
#[derive(Debug, PartialEq)]
enum CardState {
    Idle,
    Ready,
    Identification,
    Standby,
    Transfer,
    SendingData,
    ReceiveData,
    Programming,
    Disconnect,
    Unknown,
}

#[derive(Debug, Clone)]
pub enum BlockTransmissionMode {
    // Using set block count cmd for multiblock transfer
    SetBlockCount = 0,
    // Using stop transmission count cmd for multiblock transfer
    StopTransmission = 1,
    // Host automatically send stop command without the need to driver interference
    AutoStop = 2,
}

#[derive(Debug)]
pub struct CardInfo {
    pub card_id: u128,
    pub card_capacity: u64,
    pub card_state: MmcState,
}
