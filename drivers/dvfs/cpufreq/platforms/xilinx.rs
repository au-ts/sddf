// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

use core::ptr::{read_volatile, write_volatile};

use crate::freq_trait::{CoreInfo, Error, FreqOps, OppEntry};

// The memory address of ACPU controller
const ACPU_CTRL: usize = 0x00FD1A0060;
const ACPU_CTRL_DIVISOR_MASK: u32 = 0x3F00;

// When uboot boots up, the APLL clock is set to 1199999988
const APLL_CLK_FREQ: u32 = 1199999988;

pub const OPP_TABLE: &[OppEntry] = &[
    OppEntry {
        freq_hz: 1199999988,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
    OppEntry {
        freq_hz: 599999994,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
    OppEntry {
        freq_hz: 399999996,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
    OppEntry {
        freq_hz: 299999997,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
];

pub const ZCU102_CPU: &[CoreInfo] = &[
    CoreInfo {
        core_ident: 0,
        clock_source_ident: 0,
        opptable: OPP_TABLE,
    },
    CoreInfo {
        core_ident: 1,
        clock_source_ident: 0,
        opptable: OPP_TABLE,
    },
    CoreInfo {
        core_ident: 2,
        clock_source_ident: 0,
        opptable: OPP_TABLE,
    },
    CoreInfo {
        core_ident: 3,
        clock_source_ident: 0,
        opptable: OPP_TABLE,
    },
];

pub struct Xilinx {}

impl FreqOps for Xilinx {
    const CPU_OPP_TABLE: &[CoreInfo] = ZCU102_CPU;

    fn get_freq(core_ident: u64) -> Result<u64, Error> {
        if core_ident >= Self::CORE_NUM as u64 {
            return Err(Error::EINVAL);
        }

        let divisor = (unsafe { read_volatile(ACPU_CTRL as *const u32) } & ACPU_CTRL_DIVISOR_MASK)
            >> ACPU_CTRL_DIVISOR_MASK.trailing_zeros();

        Ok((APLL_CLK_FREQ / divisor) as u64)
    }

    fn set_freq(core_ident: u64, freq_hz: u64) -> Result<(), Error> {
        if core_ident < Self::CORE_NUM as u64
            && let Some(entry) = ZCU102_CPU[core_ident as usize]
                .opptable
                .iter()
                .find(|item| item.freq_hz == freq_hz)
        {
            let divisor = (APLL_CLK_FREQ as u64 / entry.freq_hz) as u32;

            unsafe {
                let register_value = read_volatile(ACPU_CTRL as *const u32);

                write_volatile(
                    ACPU_CTRL as *mut u32,
                    register_value & (!ACPU_CTRL_DIVISOR_MASK)
                        | (divisor << ACPU_CTRL_DIVISOR_MASK.trailing_zeros()),
                );
            }
            return Ok(());
        }

        Err(Error::EINVAL)
    }
}
