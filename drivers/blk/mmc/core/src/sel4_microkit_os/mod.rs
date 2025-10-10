// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

use sdmmc_protocol::sdmmc_os::{Log, Sleep};
use sel4_panicking_env::__debug_print_macro_helper;

#[cfg(feature = "meson")]
mod odroidc4;

#[cfg(feature = "meson")]
pub(crate) mod platform {
    pub(crate) use crate::sel4_microkit_os::odroidc4::{VOLTAGE, host_info, platform_hal};
}

const NS_IN_US: u64 = 1000;

/// Wrapper to work around Rust's orphan rule
pub struct TimerOps {}

impl TimerOps {
    pub const fn new() -> Self {
        TimerOps {}
    }
}

impl Sleep for TimerOps {
    fn usleep(&mut self, time_us: u32) {
        sdmmc_protocol::sdmmc_os::process_wait_unreliable(time_us as u64 * NS_IN_US);
    }
}

pub struct SerialOps {}

impl SerialOps {
    pub const fn new() -> Self {
        SerialOps {}
    }
}

impl Log for SerialOps {
    fn log(&self, args: core::fmt::Arguments) {
        __debug_print_macro_helper(args);
    }
}
