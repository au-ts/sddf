// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

use core::ptr;

use sdmmc_protocol::{
    sdmmc::{MmcPowerMode, MmcSignalVoltage, SdmmcError},
    sdmmc_os::VoltageOps,
};

use meson_hal::meson_gx_mmc::SdmmcMesonHardware;

pub struct Odroidc4VoltageSwitch;
pub(crate) const VOLTAGE: Odroidc4VoltageSwitch = Odroidc4VoltageSwitch::new();

/// Check the AO_GPIO_O_EN_N register in S905X3 datasheet
const AO_RTI_OUTPUT_ENABLE_REG: u64 = 0xff800024;
const AO_RTI_OUTPUT_LEVEL_REG: u64 = 0xff800034;
const AO_RTI_PULL_UP_EN_REG: u64 = 0xff800030;

/// Check GPIOAO_x Multi-Function Pin register in in S905X3 datasheet
/// We probably need to ensure the pinmux is set up correctly to use the correct pin func
/// Which is missing now!!! This is especially important for GPIOAO_6 as the default function
/// does not seems to be the one we want to use, for GPIO_AO_3 it should be fine as the default
/// one is the one we want to use
const GPIO_AO_3: u32 = 1 << 3;
const GPIO_AO_6: u32 = 1 << 6;

impl Odroidc4VoltageSwitch {
    pub const fn new() -> Self {
        Odroidc4VoltageSwitch {}
    }
}

impl VoltageOps for Odroidc4VoltageSwitch {
    fn card_voltage_switch(&mut self, voltage: MmcSignalVoltage) -> Result<(), SdmmcError> {
        match voltage {
            MmcSignalVoltage::Voltage330 => {
                let mut value: u32;
                unsafe {
                    value = ptr::read_volatile(AO_RTI_OUTPUT_ENABLE_REG as *const u32);
                }
                value &= !GPIO_AO_6;
                unsafe {
                    ptr::write_volatile(AO_RTI_OUTPUT_ENABLE_REG as *mut u32, value);
                }
                unsafe {
                    value = ptr::read_volatile(AO_RTI_OUTPUT_LEVEL_REG as *const u32);
                }
                value &= !GPIO_AO_6;
                unsafe {
                    ptr::write_volatile(AO_RTI_OUTPUT_LEVEL_REG as *mut u32, value);
                }
            }
            MmcSignalVoltage::Voltage180 => {
                let mut value: u32;
                unsafe {
                    value = ptr::read_volatile(AO_RTI_OUTPUT_ENABLE_REG as *const u32);
                }
                value &= !GPIO_AO_6;
                unsafe {
                    ptr::write_volatile(AO_RTI_OUTPUT_ENABLE_REG as *mut u32, value);
                }
                unsafe {
                    value = ptr::read_volatile(AO_RTI_OUTPUT_LEVEL_REG as *const u32);
                }
                value |= GPIO_AO_6;
                unsafe {
                    ptr::write_volatile(AO_RTI_OUTPUT_LEVEL_REG as *mut u32, value);
                }
            }
            MmcSignalVoltage::Voltage120 => return Err(SdmmcError::EINVAL),
        }
        // Disable pull-up/down for gpioAO_6
        let mut value: u32;

        unsafe {
            value = ptr::read_volatile(AO_RTI_PULL_UP_EN_REG as *const u32);
        }
        value &= !GPIO_AO_6;

        unsafe {
            ptr::write_volatile(AO_RTI_PULL_UP_EN_REG as *mut u32, value);
        }

        Ok(())
    }

    fn card_set_power(&mut self, power_mode: MmcPowerMode) -> Result<(), SdmmcError> {
        let mut value: u32;
        unsafe {
            value = ptr::read_volatile(AO_RTI_OUTPUT_ENABLE_REG as *const u32);
        }
        // If the GPIO pin is not being set as output, set it to output first
        if value & GPIO_AO_3 != 0 {
            value &= !GPIO_AO_3;
            unsafe {
                ptr::write_volatile(AO_RTI_OUTPUT_ENABLE_REG as *mut u32, value);
            }
        }
        match power_mode {
            MmcPowerMode::On => {
                unsafe {
                    value = ptr::read_volatile(AO_RTI_OUTPUT_LEVEL_REG as *const u32);
                }
                if value & GPIO_AO_3 == 0 {
                    value |= GPIO_AO_3;
                    unsafe {
                        ptr::write_volatile(AO_RTI_OUTPUT_LEVEL_REG as *mut u32, value);
                    }
                }
                self.card_voltage_switch(MmcSignalVoltage::Voltage330)?;
            }
            MmcPowerMode::Off => {
                unsafe {
                    value = ptr::read_volatile(AO_RTI_OUTPUT_LEVEL_REG as *const u32);
                }
                if value & GPIO_AO_3 != 0 {
                    value &= !GPIO_AO_3;
                    unsafe {
                        ptr::write_volatile(AO_RTI_OUTPUT_LEVEL_REG as *mut u32, value);
                    }
                }
            }
            _ => return Err(SdmmcError::EINVAL),
        }
        Ok(())
    }
}

pub unsafe fn platform_hal(regs_base: u64) -> SdmmcMesonHardware {
    unsafe { SdmmcMesonHardware::new(regs_base) }
}
