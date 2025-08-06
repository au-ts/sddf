use core::sync::atomic::Ordering;

use crate::{sdmmc_os::Sleep, sdmmc_traits::SdmmcHardware};

use super::{
    MMC_RSP_R1, MmcData, MmcDataFlag, SdmmcCmd, SdmmcError,
    sdcard::{Scr, Sdcard},
    sdmmc_constant::{MMC_CMD_APP_CMD, SD_CMD_APP_SEND_SCR, SD_CMD_SWITCH_FUNC},
};

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
}
