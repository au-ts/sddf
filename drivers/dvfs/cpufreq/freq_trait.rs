// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

#[derive(Debug)]
pub struct OppEntry {
    pub freq_hz: u64,
    pub voltage_uv: u64,
    pub latency_ns: u64,
}

#[derive(Debug)]
pub struct CoreInfo {
    pub core_ident: u64,
    pub clock_source_ident: u64,
    pub opptable: &'static [OppEntry],
}

#[derive(Debug)]
pub enum Error {
    EINVAL = 0,
}

pub trait FreqOps {
    const CPU_OPP_TABLE: &[CoreInfo];
    const CORE_NUM: u32 = Self::CPU_OPP_TABLE.len() as u32;

    const _CHECK_OPP_TABLE_LEN: () = {
        core::assert!(
            Self::CORE_NUM as usize == Self::CPU_OPP_TABLE.len(),
            "Mismatch between CORE_NUM and the actual length of OPP_TABLE"
        );
    };

    fn get_freq(core_ident: u64) -> Result<u64, Error> {
        core::panic!(
            "DVFS is not implemented by get request for CPU{:?}",
            core_ident
        );
    }

    fn set_freq(core_ident: u64, freq_hz: u64) -> Result<(), Error> {
        core::panic!(
            "DVFS is not implemented by get request for CPU{:?}, freq {:?} cannot be set",
            core_ident,
            freq_hz
        );
    }
}
