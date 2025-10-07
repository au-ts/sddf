// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

use crate::{
    dev_log,
    sdmmc::{
        HostInfo, MmcData, MmcIos, MmcSignalVoltage, SdmmcCmd, SdmmcError,
        mmc_struct::{MmcBusWidth, MmcTiming},
    },
    sdmmc_os::Sleep,
};

// const POLLING_INTERVAL_TIME_US: u32 = 1024;
const DATA_TRANSFER_POLLING_INTERVAL_TIME_US: u32 = 4096;

// The polling chances before time out is deliberately being set to a large value
//  as the host is supposed to catch thetimeout request and report to us
const POLLING_CHANCE_BEFORE_TIME_OUT: u32 = 10240;
const DATA_TRANSFER_POLLING_CHANCE_BEFORE_TIME_OUT: u32 = 2048;

#[allow(unused_variables)]
pub trait SdmmcOps {
    fn sdmmc_init(&mut self) -> Result<MmcIos, SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    /// Change the clock, return the value or do not change it at all
    /// If the freq is set to zero, this function should try to stop the clock completely
    /// Beware at higher frequency, you may need to play with delay, adjust and clock phase
    /// to ensure that the clock edges (sampling points) occur just in time for the valid data window.
    fn sdmmc_config_timing(&mut self, timing: MmcTiming) -> Result<u64, SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    fn sdmmc_config_bus_width(&mut self, bus_width: MmcBusWidth) -> Result<(), SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    /// Reads the current state of the SD card data lanes.
    ///
    /// This function is specifically used during voltage switching to check if the SD card
    /// acknowledges the switch by setting the data signal to low or high.
    ///
    /// Returns:
    /// - `u8`: The current state of the data lanes, where each bit represents a data line:
    ///   - `DAT0` corresponds to the least significant bit (LSB).
    ///   - `DAT7` corresponds to the most significant bit (MSB).
    ///
    /// Note:
    /// - This function is not yet implemented and currently returns an `ENOTIMPLEMENTED` error.
    fn sdmmc_read_datalanes(&self) -> Result<u8, SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    /// Sends a command to the SD/MMC card, ensuring that busy signal handling is managed appropriately.
    ///
    /// ### Busy Signal Handling
    /// The hardware layer is responsible for delaying the actual sending of the command if the card is busy.
    /// For example, when the protocol layer sends a command expecting an R1B response (which indicates a busy state),
    /// and immediately sends another command afterward, the hardware layer must ensure that the new command is sent
    /// only after the busy signal from the card has cleared.
    ///
    /// ### Hardware Busy Signal Detection
    /// Many modern host controllers support automatic busy signal detection, in which case the hardware layer
    /// does not need to implement any additional checks or delays—the controller will wait internally until
    /// the busy state is cleared before completing the command.
    ///
    /// ### Manual Busy Waiting
    /// If the host controller does not support hardware busy signal detection, the hardware layer must
    /// implement this behavior manually by monitoring the card's busy state and delaying the next command
    /// until the card is ready. This approach aligns with Linux’s handling of busy signals in its MMC/SD subsystem.
    ///
    /// ### Parameters
    /// * `cmd` - The SD/MMC command to send.
    /// * `data` - Optional data associated with the command, if applicable.
    ///
    /// ### Returns
    /// * `Ok(())` on success.
    /// * `Err(SdmmcError::ENOTIMPLEMENTED)` if the function is not implemented.
    ///
    fn sdmmc_send_command(
        &mut self,
        cmd: &SdmmcCmd,
        data: Option<&MmcData>,
    ) -> Result<(), SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    fn sdmmc_receive_response(
        &self,
        cmd: &SdmmcCmd,
        response: &mut [u32; 4],
    ) -> Result<(), SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    // Change the function signature to something like sdmmc_config_interrupt(&mut self, enable_irq: bool, enable_sdio_irq: bool);
    fn sdmmc_config_interrupt(
        &mut self,
        enable_irq: bool,
        enable_sdio_irq: bool,
    ) -> Result<(), SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    fn sdmmc_ack_interrupt(&mut self) -> Result<(), SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    /// At higher clock frequencies, timing mismatches can occur between the host's sampling point and the valid data window
    /// from the SD card during read operations. This can lead to CRC errors, as the host may sample incoming data outside the
    /// stable data window, even when the SD card’s response appears normal.
    ///
    /// To address this, the `sdmmc_tune_sampling` function is introduced. This function aims to adjust the host's sampling
    /// timing to align with the SD card’s data output window, reducing errors caused by timing misalignment.
    ///
    /// In some cases, a similar function (e.g., `sdmmc_tune_sending_data_window`) may be needed to tune the timing of data
    /// signals sent from the host to the SD card. This would ensure that the SD card reliably receives data, especially
    /// at high frequencies. However, output timing tends to be more stable, and a specific function for tuning host-to-card
    /// data timing is often not implemented or needed, as seen in the Linux driver.
    fn sdmmc_execute_tuning(
        &mut self,
        memory: *mut [u8; 64],
        sleep: &mut dyn Sleep,
    ) -> Result<(), SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    fn sdmmc_host_reset(&mut self) -> Result<MmcIos, SdmmcError> {
        Err(SdmmcError::ENOTIMPLEMENTED)
    }

    /// This function implements the bare metal version of adjust signaling voltage
    /// If in the SdmmcProtocol::new() function, there are different voltage switch
    /// methods provided, this sdmmc_voltage_switch function will not be used
    /// Power cycling is assumed in host reset function if voltage_switch is implemented here
    fn sdmmc_voltage_switch(&mut self, voltage: MmcSignalVoltage) -> Result<(), SdmmcError> {
        // Default behavior should be rushing instead of returning one error
        panic!("sdmmc: voltage switch is not implemented!")
    }

    fn sdmmc_do_request(
        &mut self,
        sleep: &mut dyn Sleep,
        cmd: &SdmmcCmd,
        data: Option<&MmcData>,
        resp: &mut [u32; 4],
        mut retry: u32,
    ) -> Result<(), SdmmcError> {
        'command_retry: loop {
            // Send the command using send command function provided by the hardware layer
            self.sdmmc_send_command(cmd, data)?;

            let mut res: Result<(), SdmmcError>;

            match data {
                // The flow with data transfer
                Some(_) => {
                    for _ in 0..DATA_TRANSFER_POLLING_CHANCE_BEFORE_TIME_OUT {
                        sleep.usleep(DATA_TRANSFER_POLLING_INTERVAL_TIME_US);
                        res = self.sdmmc_receive_response(cmd, resp);
                        match res {
                            Err(SdmmcError::ETIMEDOUT) => {
                                if retry == 0 {
                                    return Err(SdmmcError::ETIMEDOUT);
                                }
                                retry -= 1;
                                continue 'command_retry;
                            }
                            Err(SdmmcError::EBUSY) => continue,
                            Err(e) => return Err(e),
                            Ok(_) => return Ok(()),
                        }
                    }
                }
                // The flow without data transfer
                None => {
                    for _ in 0..POLLING_CHANCE_BEFORE_TIME_OUT {
                        // There seems to be card that are actually time-sensitive to certain command
                        // Like if the driver polling the voltage switch command too slow and switch voltage a bit late
                        // Card will not switch voltage successfully.
                        // So choosing the fitting polling interval here is very important to correctness
                        // For correctness reason, right now we don't add any polling interval
                        // process_wait_unreliable(POLLING_INTERVAL_TIME_US as u64 * 1000);
                        res = self.sdmmc_receive_response(cmd, resp);
                        match res {
                            Err(SdmmcError::ETIMEDOUT) => {
                                if retry == 0 {
                                    return Err(SdmmcError::ETIMEDOUT);
                                }
                                retry -= 1;
                                continue 'command_retry;
                            }
                            Err(SdmmcError::EBUSY) => continue,
                            Err(e) => return Err(e),
                            Ok(_) => return Ok(()),
                        }
                    }
                }
            }
            break 'command_retry;
        }
        dev_log!("A timeout request not reported by the host, the host might be unreliable\n");
        Err(SdmmcError::EUNDEFINED)
    }
}

#[allow(unused_variables)]
/// Trait to be implemented by the sdcard hal
pub trait SdmmcHardware: SdmmcOps {
    const HOST_INFO: HostInfo;

    /// This function is NOT meant for initialization of the host
    /// It should be marked as const once the const traits feature in Rust is stable
    unsafe fn new(sdmmc_register_base: u64) -> Self;
}
