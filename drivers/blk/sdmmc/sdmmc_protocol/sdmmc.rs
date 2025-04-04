use core::{
    future::Future,
    pin::Pin,
    sync::atomic::Ordering,
    task::{Context, Poll, Waker},
};

use mmc_struct::{BlockTransmissionMode, MmcBusWidth, MmcDevice, MmcState, MmcTiming, TuningState};
use sdcard::{Cid, Csd, Scr, Sdcard};
use sdmmc_capability::{
    SdcardCapability, SdmmcHostCapability, MMC_CAP_4_BIT_DATA, MMC_CAP_VOLTAGE_TUNE, MMC_EMPTY_CAP,
    MMC_TIMING_LEGACY, MMC_TIMING_SD_HS, MMC_TIMING_UHS_DDR50, MMC_TIMING_UHS_SDR104,
    MMC_TIMING_UHS_SDR12, MMC_TIMING_UHS_SDR25, MMC_TIMING_UHS_SDR50,
};
use sdmmc_constant::{
    MMC_CMD_ALL_SEND_CID, MMC_CMD_APP_CMD, MMC_CMD_ERASE, MMC_CMD_GO_IDLE_STATE,
    MMC_CMD_READ_MULTIPLE_BLOCK, MMC_CMD_READ_SINGLE_BLOCK, MMC_CMD_SELECT_CARD, MMC_CMD_SEND_CSD,
    MMC_CMD_SET_BLOCK_COUNT, MMC_CMD_STOP_TRANSMISSION, MMC_CMD_WRITE_MULTIPLE_BLOCK,
    MMC_CMD_WRITE_SINGLE_BLOCK, OCR_BUSY, OCR_HCS, OCR_S18R, SD_CMD_APP_SEND_OP_COND,
    SD_CMD_APP_SET_BUS_WIDTH, SD_CMD_ERASE_WR_BLK_END, SD_CMD_ERASE_WR_BLK_START,
    SD_CMD_SEND_IF_COND, SD_CMD_SEND_RELATIVE_ADDR, SD_CMD_SWITCH_FUNC, SD_CMD_SWITCH_UHS18V,
    SD_ERASE_ARG, SD_SWITCH_FUNCTION_GROUP_ONE, SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_SDHS,
    SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_DDR50, SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR104,
    SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR12, SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR25,
    SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR50, SD_SWITCH_FUNCTION_GROUP_ONE_SET_LEGACY,
    SD_SWITCH_FUNCTION_GROUP_ONE_SET_SDHS, SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_DDR50,
    SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR104, SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR12,
    SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR25, SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR50,
    SD_SWITCH_FUNCTION_SELECTION_GROUP_ONE,
};

use crate::sdmmc_traits::SdmmcHardware;

use crate::sdmmc_os::{debug_log, process_wait_unreliable};

pub mod mmc_struct;
pub mod sd_ops;
pub mod sdcard;
pub mod sdmmc_capability;
mod sdmmc_constant;

pub struct SdmmcCmd {
    pub cmdidx: u32,
    pub resp_type: u32,
    pub cmdarg: u32,
}

pub struct MmcData {
    // The size of the block(sector size), for sdcard should almost always be 512
    pub blocksize: u32,
    // Number of blocks to transfer
    pub blockcnt: u32,
    pub flags: MmcDataFlag,
    pub addr: u64,
}

pub enum MmcDataFlag {
    SdmmcDataRead,
    SdmmcDataWrite,
}

#[derive(Debug)]
pub enum SdmmcError {
    // Error for result not ready yet
    EBUSY,
    ETIMEDOUT,
    EINVAL,
    EIO,
    // Error that I currently not sure how to deal with...
    EUNKNOWN,
    EUNSUPPORTEDCARD,
    ENOTIMPLEMENTED,
    // This error should not be triggered unless there are bugs in program
    EUNDEFINED,
    // The block transfer succeed, but fail to stop the read/write process
    ESTOPCMD,
    ENOCARD,
    ECARDINACTIVE,
}

// Define the MMC response flags
const MMC_RSP_PRESENT: u32 = 1 << 0;
const MMC_RSP_136: u32 = 1 << 1; // 136-bit response
const MMC_RSP_CRC: u32 = 1 << 2; // Expect valid CRC
const MMC_RSP_BUSY: u32 = 1 << 3; // Card may send busy
const MMC_RSP_OPCODE: u32 = 1 << 4; // Response contains opcode

// Define the MMC response types
pub const MMC_RSP_NONE: u32 = 0;
pub const MMC_RSP_R1: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;
pub const MMC_RSP_R1B: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE | MMC_RSP_BUSY;
pub const MMC_RSP_R2: u32 = MMC_RSP_PRESENT | MMC_RSP_136 | MMC_RSP_CRC;
pub const MMC_RSP_R3: u32 = MMC_RSP_PRESENT;
pub const MMC_RSP_R4: u32 = MMC_RSP_PRESENT;
pub const MMC_RSP_R5: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;
pub const MMC_RSP_R6: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;
pub const MMC_RSP_R7: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;

// Enums for power_mode
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MmcPowerMode {
    Off = 0,
    On = 1,
    Undefined = 2,
}

// Signal voltage
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MmcSignalVoltage {
    Voltage330 = 0,
    Voltage180 = 1,
    Voltage120 = 2,
}

// Driver type
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MmcDriverType {
    TypeB = 0,
    TypeA = 1,
    TypeC = 2,
    TypeD = 3,
}

// Enums for chip_select
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MmcChipSelect {
    DontCare = 0,
    High = 1,
    Low = 2,
}

/// Settings specific to eMMC cards.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmmcSettings {
    /// The drive strength of the host driver, typically relevant for eMMC devices.
    ///
    /// - The drive strength affects signal integrity and is selected based on the card's
    ///   operating conditions, such as bus load and speed.
    /// - The eMMC specification defines four possible driver types (A, B, C, D) that
    ///   optimize for different use cases and electrical environments:
    ///   - `DriverType::TypeB`: Default driver strength for most cases.
    ///   - `DriverType::TypeA`, `TypeC`, `TypeD`: Other driver types based on signal
    ///     strength requirements.
    pub drv_type: MmcDriverType,

    /// Specifies whether **HS400 Enhanced Strobe** mode is enabled.
    ///
    /// - Enhanced Strobe is used in **HS400** mode for eMMC devices to improve data
    ///   reliability at high speeds. It allows more accurate data capture by aligning
    ///   strobe signals with data.
    /// - This is only relevant for eMMC cards in **HS400ES** mode.
    pub enhanced_strobe: bool,
}

/// Settings specific to SPI communication mode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpiSettings {
    /// The chip select mode used in **SPI mode** communication.
    ///
    /// - This field is relevant only when the SD/MMC host controller is operating in **SPI mode**.
    ///   In **native SD/MMC protocol**, this field is not used.
    ///
    /// - The **chip select (CS)** pin is used to activate or deactivate the SD/MMC card on the SPI bus.
    ///   It allows the host to select which device it is communicating with when multiple devices share the same bus.
    ///
    /// - Possible values:
    ///   - `MmcChipSelect::DontCare`: The chip select state is ignored by the host.
    ///   - `MmcChipSelect::High`: The chip select pin is driven high, indicating that the card is not selected.
    ///   - `MmcChipSelect::Low`: The chip select pin is driven low, indicating that the card is selected and active.
    ///
    /// **Note**:
    /// - In **native SD/MMC mode**, communication happens via dedicated **command and data lines** without the need for chip select.
    /// - In most applications, **SPI mode** is less commonly used, especially in high-performance systems.
    pub chip_select: MmcChipSelect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// The `MmcIos` struct represents the I/O settings for the SD/MMC controller,
/// configuring how the host communicates with the card during various operations.
pub struct MmcIos {
    /// The clock rate (in Hz) used for communication with the SD/MMC card.
    ///
    /// - This field specifies the frequency at which data is transferred between
    ///   the host and the card. The clock can vary depending on the mode the card
    ///   is in (e.g., initialization, data transfer).
    /// - Typically, initialization occurs at a lower clock rate, and high-speed
    ///   data transfer occurs at higher rates.
    pub clock: u64,

    /// The current power supply mode for the SD/MMC card.
    ///
    /// - This field indicates whether the card is powered on, powered off, or
    ///   being powered up. The power mode can affect the card's internal state
    ///   and availability for communication.
    /// - Possible values:
    ///   - `PowerMode::Off`: The card is completely powered off.
    ///   - `PowerMode::Up`: The card is in the process of powering up.
    ///   - `PowerMode::On`: The card is fully powered and ready for communication.
    pub power_mode: MmcPowerMode,

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

    /// The signaling voltage level used for communication with the card.
    ///
    /// - Different SD/MMC cards support different signaling voltage levels. This field
    ///   indicates the voltage level used for signaling between the host and the card.
    /// - Common voltage levels:
    ///   - `SignalVoltage::Voltage330`: 3.3V signaling.
    ///   - `SignalVoltage::Voltage180`: 1.8V signaling.
    ///   - `SignalVoltage::Voltage120`: 1.2V signaling (mainly for newer eMMC devices).
    pub signal_voltage: MmcSignalVoltage,

    /// Indicating if interrupt is enabled or not
    pub enabled_irq: bool,

    /// eMMC-specific settings, if applicable.
    ///
    /// This field is `None` if the card is not an eMMC card.
    pub emmc: Option<EmmcSettings>,

    /// SPI-specific settings, if applicable.
    ///
    /// This field is `None` if the card is not operating in SPI mode.
    pub spi: Option<SpiSettings>,
}

#[derive(Debug, Clone)]
pub struct HostInfo {
    pub max_frequency: u64,
    pub min_frequency: u64,
    pub max_block_per_req: u32,
    /// The voltage range (VDD) used for powering the SD/MMC card.
    ///
    /// - This field stores the selected voltage range in a bit-encoded format.
    ///   It indicates the voltage level the card is operating at.
    /// - Common voltage levels are 3.3V, 1.8V, and sometimes 1.2V (for eMMC).
    /// - Cards often negotiate their operating voltage during initialization.
    pub vdd: u32,

    /// The power delay (in milliseconds) used after powering the card to ensure
    /// stable operation.
    ///
    /// - After powering up the card, the host controller typically waits for a
    ///   certain period before initiating communication to ensure that the card's
    ///   power supply is stable.
    /// - This delay ensures the card is ready to respond to commands.
    pub power_delay_ms: u32,
}

/// TODO: Add more variables for SdmmcProtocol to track the state of the sdmmc controller and card correctly
pub struct SdmmcProtocol<T: SdmmcHardware> {
    pub hardware: T,

    mmc_ios: MmcIos,

    host_info: HostInfo,

    host_capability: SdmmcHostCapability,

    /// This mmc device is optional because there may not always be a card in the slot!
    mmc_device: Option<MmcDevice>,

    private_memory: Option<*mut [u8; 64]>,
}

impl<T> Unpin for SdmmcProtocol<T> where T: Unpin + SdmmcHardware {}

impl<T: SdmmcHardware> SdmmcProtocol<T> {
    pub fn new(mut hardware: T) -> Result<Self, SdmmcError> {
        let (ios, info, cap) = hardware.sdmmc_init()?;

        Ok(SdmmcProtocol {
            hardware,
            mmc_ios: ios,
            host_info: info,
            host_capability: SdmmcHostCapability(cap),
            mmc_device: None,
            private_memory: None,
        })
    }

    fn sdcard_init(&mut self, voltage_switch: bool) -> Result<(), SdmmcError> {
        let mut resp: [u32; 4] = [0; 4];

        let mut cmd = SdmmcCmd {
            cmdidx: MMC_CMD_GO_IDLE_STATE,
            resp_type: MMC_RSP_NONE,
            cmdarg: 0,
        };

        debug_log!("Try to send go idle cmd\n");

        // Go idle command does not expect a response
        self.hardware.sdmmc_send_command(&cmd, None)?;

        // Linux use 1ms delay here, we use 2ms
        process_wait_unreliable(2_000_000);

        debug_log!("Try to send check operating voltage cmd\n");

        cmd = SdmmcCmd {
            cmdidx: SD_CMD_SEND_IF_COND,
            resp_type: MMC_RSP_R7,
            cmdarg: 0x000001AA, // Voltage supply and check pattern
        };

        let res: Result<(), SdmmcError> = self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 1);

        // If the result is OK and the resp is 0x1AA, the card we are initializing is a SDHC/SDXC
        // If the result is error, it is either the voltage not being set up correctly, which mean a bug in hardware layer
        // or the card is eMMC or legacy sdcard
        // For now, we only deal with the situation it is a sdcard
        if res.is_ok() && resp[0] != 0x1AA {
            return Err(SdmmcError::EUNSUPPORTEDCARD);
        }

        // Uboot define this value to 1000...
        let mut retry: u16 = 1000;

        loop {
            debug_log!("Sending SD_CMD_APP_SEND_OP_COND!\n");
            // Prepare CMD55 (APP_CMD)
            cmd = SdmmcCmd {
                cmdidx: MMC_CMD_APP_CMD,
                resp_type: MMC_RSP_R1,
                cmdarg: 0,
            };

            // Send CMD55
            let res = self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 0);

            match res {
                Ok(_) => {}
                Err(SdmmcError::ETIMEDOUT) => return Err(SdmmcError::EUNSUPPORTEDCARD),
                Err(_) => return res,
            }

            cmd = SdmmcCmd {
                cmdidx: SD_CMD_APP_SEND_OP_COND,
                resp_type: MMC_RSP_R3,
                cmdarg: 0,
            };

            // Set the HCS bit if version is SD Version 2
            // Since we are only support SDHC card, the OCR_HCS bit should be supported by the card
            cmd.cmdarg |= OCR_HCS;

            // Right now we deliberately not set XPC bit for maximum compatibility

            // Change this when we decide to support spi or SDSC as well
            cmd.cmdarg |= self.host_info.vdd & 0xff8000;

            if self
                .host_capability
                .contains(sdmmc_capability::SdmmcHostCapability(
                    MMC_TIMING_UHS_SDR12 | MMC_CAP_VOLTAGE_TUNE,
                ))
            {
                cmd.cmdarg |= OCR_S18R;
                // It seems that cards will not respond to commands that have MMC_VDD_165_195 bit set, even if the card supports UHS-I
                // cmd.cmdarg |= MMC_VDD_165_195;
            }

            // Send ACMD41
            self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 0)?;

            debug_log!("OCR: {:08x}\n", resp[0]);

            // Check if card is ready (OCR_BUSY bit)
            if (resp[0] & OCR_BUSY) != 0 {
                break;
            }

            // retry handling
            if retry <= 0 {
                debug_log!("SDMMC: SEND_OP_COND failed, card not supported!\n");
                return Err(SdmmcError::EUNSUPPORTEDCARD);
            }
            retry -= 1;
        }

        // Checking if the host and card is eligible for voltage switch
        if self
            .host_capability
            .contains(sdmmc_capability::SdmmcHostCapability(MMC_TIMING_UHS_SDR12))
            && voltage_switch == true
            && resp[0] & OCR_HCS == OCR_HCS
            && resp[0] & OCR_S18R == OCR_S18R
        {
            // TODO: If the sdcard fail at this stage, a power circle and reinit should be performed
            self.tune_sdcard_switch_uhs18v()?;
            self.mmc_ios.signal_voltage = MmcSignalVoltage::Voltage180;
        }

        Ok(())
    }

    fn sdmmc_power_cycle(&mut self) -> Result<(), SdmmcError> {
        self.hardware.sdmmc_set_power(MmcPowerMode::Off)?;
        process_wait_unreliable(self.host_info.power_delay_ms as u64 * 1_000_000);

        self.hardware.sdmmc_set_power(MmcPowerMode::On)?;
        process_wait_unreliable(1_000_000);

        self.mmc_ios.power_mode = MmcPowerMode::On;
        Ok(())
    }

    // Funtion that is not completed
    pub fn setup_card(&mut self) -> Result<(), SdmmcError> {
        // Disable all irqs here
        self.hardware.sdmmc_config_interrupt(false, false)?;

        // TODO: Different sdcard and eMMC support different voltages, figure those out
        if self.mmc_ios.power_mode != MmcPowerMode::On {
            debug_log!("Turn the power up");
            self.hardware.sdmmc_set_power(MmcPowerMode::On)?;
            // TODO: Right now we know the power will always be up and this function should not be called
            // But when we encounter scenerio that may actually call this function, we should wait for the time specified in ios
            // Right now this whole power up related thing does not work
            process_wait_unreliable(self.host_info.power_delay_ms as u64 * 1_000_000);

            self.mmc_ios.power_mode = MmcPowerMode::On;
        }

        let clock = self.hardware.sdmmc_config_timing(MmcTiming::CardSetup)?;

        self.mmc_ios.clock = clock;

        // This line of code may not be needed?
        self.hardware.sdmmc_config_bus_width(MmcBusWidth::Width1)?;

        self.mmc_ios.bus_width = MmcBusWidth::Width1;

        let mut voltage_switch: bool = true;

        // Use labeled block here for better clarification
        // There could be more complex retry logic implemented in the future
        'sdcard_init: loop {
            match self.sdcard_init(voltage_switch) {
                Ok(()) => {}
                Err(SdmmcError::EUNSUPPORTEDCARD) => {
                    break 'sdcard_init;
                }
                Err(_) => {
                    if voltage_switch == true {
                        voltage_switch = false;

                        // Retry with voltage switch off
                        debug_log!("Try to init the card without voltage switch\n");
                        self.sdmmc_power_cycle()?;

                        self.mmc_ios = self.hardware.sdmmc_host_reset()?;

                        // One bug that does not break anything here is
                        // sdmmc_host_reset will reset the clock to CardSetup timing and turn off the irq
                        // But those variable in mmc_ios is not changed accordingly

                        continue 'sdcard_init;
                    } else {
                        break 'sdcard_init;
                    }
                }
            }

            let card: Sdcard = self.setup_sdcard_cont()?;
            self.mmc_device = Some(MmcDevice::Sdcard(card));
            return Ok(());
        }

        // Unsupported card
        {
            // If the result is error, it is either the voltage not being set up correctly, which mean a bug in hardware layer
            // or the card is eMMC or legacy sdcard
            // For now, we only deal with the situation it is a sdcard
            // TODO: Implement setup for eMMC and legacy sdcard(SDSC) here
            debug_log!("Driver right now only support SDHC/SDXC card, please check if you are running this driver on SDIO/SDSC/EMMC card!\n");
            Err(SdmmcError::EUNSUPPORTEDCARD)
        }
    }

    /// From uboot
    /// Most cards do not answer if some reserved bits
    /// in the ocr are set. However, Some controller
    /// can set bit 7 (reserved for low voltages), but
    /// how to manage low voltages SD card is not yet
    /// specified.
    /// Check mmc_sd_get_cid() in Linux for card init process
    fn setup_sdcard_cont(&mut self) -> Result<Sdcard, SdmmcError> {
        let mut resp: [u32; 4] = [0; 4];

        // Send CMD2 to get the CID register
        let mut cmd = SdmmcCmd {
            cmdidx: MMC_CMD_ALL_SEND_CID,
            resp_type: MMC_RSP_R2,
            cmdarg: 0,
        };
        self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 1)?;

        let cid: Cid = Cid::new(resp);

        let card_id = ((resp[0] as u128) << 96)
            | ((resp[1] as u128) << 64)
            | ((resp[2] as u128) << 32)
            | (resp[3] as u128);

        // TODO: Figure out a better way to do this than adding microkit crate
        debug_log!(
            "CID: {:08x} {:08x} {:08x} {:08x}\n",
            resp[0],
            resp[1],
            resp[2],
            resp[3]
        );

        // Send CMD3 to set and receive the RCA
        cmd = SdmmcCmd {
            cmdidx: SD_CMD_SEND_RELATIVE_ADDR,
            resp_type: MMC_RSP_R6,
            cmdarg: 0,
        };

        self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 1)?;

        let rca: u16 = (resp[0] >> 16) as u16; // Store RCA from response

        debug_log!("RCA: {:04x}\n", rca);

        // Send CMD9 to get the CSD register
        cmd = SdmmcCmd {
            cmdidx: MMC_CMD_SEND_CSD,
            resp_type: MMC_RSP_R2,
            cmdarg: (rca as u32) << 16,
        };

        self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 1)?;

        debug_log!(
            "CSD: {:08x} {:08x} {:08x} {:08x}\n",
            resp[0],
            resp[1],
            resp[2],
            resp[3]
        );

        let (csd, card_version) = Csd::new(resp);

        // Send CMD7 to select the card
        cmd = SdmmcCmd {
            cmdidx: MMC_CMD_SELECT_CARD,
            resp_type: MMC_RSP_R1,
            cmdarg: (rca as u32) << 16,
        };

        self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 1)?;

        // SDHC/SDXC default to 512 bytes sector size so I did not manually set it here

        self.mmc_ios.clock = self.hardware.sdmmc_config_timing(MmcTiming::Legacy)?;

        let card_state: MmcState = MmcState {
            timing: MmcTiming::Legacy,
            bus_width: MmcBusWidth::Width1,
        };

        // Continue working on it next week
        Ok(Sdcard {
            card_id,
            manufacture_info: cid,
            card_specific_data: csd,
            card_version,
            relative_card_addr: rca,
            card_state,
            card_cap: sdmmc_capability::SdcardCapability(MMC_EMPTY_CAP),
            method: BlockTransmissionMode::StopTransmission,
            card_config: None,
        })
    }

    /// A function that tune the card speed
    /// This function does not do roll back so if this function return an error, reset up the card
    /// Do NOT call this function again if your card is already tuned as this function is not that cheap!
    /// But you should call this function the card being turned into power saving mode
    /// `stolen_memory` is a specific memory region used to read data from the SD card through CMD6.
    /// To use this function safely, the memory pointer passed in must be from a valid memory address
    /// And must match the physical memory address that is being DMA into
    ///
    /// ### Important Considerations:
    ///
    /// 1. **Memory Region Constraints**:
    ///    - `stolen_memory` is used as a buffer to hold the 64-byte response from the SD card
    ///      when executing CMD6. This response contains the function switch status and other
    ///      function-related information.
    ///    - The memory region from `stolen_memory` to `stolen_memory + 64 bytes` must not overlap
    ///      with any other data structures, device registers, or memory-mapped peripherals to
    ///      avoid conflicts or unintended behavior.
    ///
    /// 2. **Cache Considerations**:
    ///    - If the system uses caching, you may need to ensure that cache effects do not interfere
    ///      with the integrity of the data read from the SD card.
    ///    - If caching is enabled, consider using cache invalidation before reading and cache flushing
    ///      after writing data to ensure consistency between the memory and the SD card.
    ///      For example, you might need to use cache control instructions or APIs specific to your
    ///      platform to manage this.
    ///
    /// 3. **Alignment and Access Requirements**:
    ///    - `stolen_memory` should be aligned to at least 4 bytes (or preferably 8 bytes) to avoid
    ///      misaligned memory access issues, which could lead to performance penalties or even faults
    ///      on some architectures.
    /// Tunes SD card performance by adjusting data bus width and speed mode.
    ///
    /// # Parameters
    /// - `addr_and_invalidate_cache_fn`: An optional tuple containing:
    ///     - `*mut [u8; 64]`: A memory address used as a buffer for certain commands (e.g., CMD6). The memory
    ///       should be suitable for DMA into(e.g. aligned to 8 bytes memory border and not conflict
    ///       with other structure or device registers).
    ///     - `fn()`: A function pointer that, when called, invalidates the cache for the range
    ///       `addr` to `addr + 64 bytes`. This function should ensure cache consistency for
    ///       that specific memory range. If `None`, no buffer is used, and the tune performance function
    ///       will not attempt to change the card speed class. The fn should not take any variables and would
    ///       not be stored. By this way, the protocol layer only has the minimal privilege it required for cache invalidation.
    ///
    /// # Returns
    /// - `Result<(), SdmmcError>`: `Ok(())` if tuning was successful, or an error otherwise.
    /// UB here waiting to be fixed: memory being a mutable reference is also accessed by DMA
    pub unsafe fn tune_performance(
        &mut self,
        memory: *mut [u8; 64],
        cache_invalidate_function: fn(),
        physical_memory_addr: u64,
    ) -> Result<(), SdmmcError> {
        // For testing
        let mmc_device = self.mmc_device.as_mut().ok_or(SdmmcError::ENOCARD)?;

        // Turn down the clock frequency
        self.mmc_ios.clock = self.hardware.sdmmc_config_timing(MmcTiming::CardSetup)?;

        // The private memory should be the physically memory
        // However any attempt to dereference the pointer
        // could crash the program if the driver don't have access
        // to the phyical memory at the proper address
        self.private_memory = Some(physical_memory_addr as *mut [u8; 64]);

        match mmc_device {
            MmcDevice::Sdcard(sdcard) => {
                sdcard.card_state.timing = MmcTiming::CardSetup;
                self.tune_sdcard_performance(
                    memory,
                    cache_invalidate_function,
                    physical_memory_addr,
                )
            }
            MmcDevice::EMmc(emmc) => Err(SdmmcError::ENOTIMPLEMENTED),
            MmcDevice::Unknown => Err(SdmmcError::ENOTIMPLEMENTED),
        }
    }

    pub fn get_host_info(&mut self) -> HostInfo {
        self.host_info.clone()
    }

    pub fn test_read_one_block(&mut self, start_idx: u64, destination: u64) {
        let data: MmcData = MmcData {
            blocksize: 512,
            blockcnt: 1,
            flags: MmcDataFlag::SdmmcDataRead,
            addr: destination,
        };
        debug_log!("Gonna test read one block!\n");
        let mut resp: [u32; 4] = [0; 4];
        let cmd_arg: u64 = start_idx;
        let cmd = SdmmcCmd {
            cmdidx: MMC_CMD_READ_SINGLE_BLOCK,
            resp_type: MMC_RSP_R1,
            cmdarg: cmd_arg as u32,
        };
        if let Err(error) = self
            .hardware
            .sdmmc_do_request(&cmd, Some(&data), &mut resp, 0)
        {
            debug_log!("Error in reading\n");
        }
        unsafe { print_one_block(destination as *mut u8, 512) };
    }

    /// Switch voltage function
    fn tune_sdcard_switch_uhs18v(&mut self) -> Result<(), SdmmcError> {
        debug_log!("Entering tune sdcard signal voltage function!\n");
        let mut resp: [u32; 4] = [0; 4];
        let cmd = SdmmcCmd {
            cmdidx: SD_CMD_SWITCH_UHS18V,
            resp_type: MMC_RSP_R1,
            cmdarg: 0, // Argument for 4-bit mode (0 for 1-bit mode)
        };

        self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 0)?;

        debug_log!("Switch voltage prepared!\n");

        self.mmc_ios.clock = self.hardware.sdmmc_config_timing(MmcTiming::ClockStop)?;

        // TODO: figuring out the optimal delay
        process_wait_unreliable(100_000);

        let mut signal: u8 = 0xFF;

        for _ in 0..100 {
            signal = self.hardware.sdmmc_read_datalanes()?;
            // TODO: figuring out the optimal delay
            process_wait_unreliable(100_000);
            debug_log!("data signal value: 0b{:b}\n", signal);
            if signal & 0xF == 0x0 {
                break;
            }
        }

        if signal & 0xF != 0x0 {
            return Err(SdmmcError::ECARDINACTIVE);
        }

        self.hardware
            .sdmmc_set_signal_voltage(MmcSignalVoltage::Voltage180)?;

        // TODO: figuring out the optimal delay
        process_wait_unreliable(10_000_000);

        self.mmc_ios.clock = self.hardware.sdmmc_config_timing(MmcTiming::CardSetup)?;

        // TODO: figuring out the optimal delay
        process_wait_unreliable(100_000);

        for _ in 0..100 {
            signal = self.hardware.sdmmc_read_datalanes()?;
            // TODO: figuring out the optimal delay
            process_wait_unreliable(100_000);
            debug_log!("data signal value: 0b{:b}\n", signal);
            if signal & 0xF == 0xF {
                break;
            }
        }

        if signal & 0xF != 0xF {
            self.hardware
                .sdmmc_set_signal_voltage(MmcSignalVoltage::Voltage330)?;
            process_wait_unreliable(1_000_000);
            return Err(SdmmcError::ECARDINACTIVE);
        }

        Ok(())
    }

    /// Right now the speed switch is done hackily
    /// The speed switch is hardcoded to switch to UHS SDR104
    /// If the card does not support UHS SDR104, the switch will fail!
    /// Implement this sdcard switch function to avoid this hackiness!
    /// Like first get the speed classes the sdcard support by this function
    /// and then switch to the proper speed class!
    unsafe fn sdcard_switch_speed(
        &mut self,
        target: MmcTiming,
        raw_memory: *mut [u8; 64],
        invalidate_cache_fn: fn(),
        physical_memory_addr: u64,
    ) -> Result<(), SdmmcError> {
        let data: MmcData = MmcData {
            blocksize: 64,
            blockcnt: 1,
            flags: MmcDataFlag::SdmmcDataRead,
            addr: physical_memory_addr,
        };

        let mut resp: [u32; 4] = [0; 4];

        // As this function only change speed class,
        let mut cmdarg: u32 = 0x80FFFFF0;
        match target {
            MmcTiming::Legacy => cmdarg |= SD_SWITCH_FUNCTION_GROUP_ONE_SET_LEGACY as u32,
            MmcTiming::SdHs => cmdarg |= SD_SWITCH_FUNCTION_GROUP_ONE_SET_SDHS as u32,
            MmcTiming::UhsSdr12 => cmdarg |= SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR12 as u32,
            MmcTiming::UhsSdr25 => cmdarg |= SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR25 as u32,
            MmcTiming::UhsSdr50 => cmdarg |= SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR50 as u32,
            MmcTiming::UhsSdr104 => cmdarg |= SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_SDR104 as u32,
            MmcTiming::UhsDdr50 => cmdarg |= SD_SWITCH_FUNCTION_GROUP_ONE_SET_UHS_DDR50 as u32,
            _ => return Err(SdmmcError::EUNDEFINED),
        }
        let cmd = SdmmcCmd {
            cmdidx: SD_CMD_SWITCH_FUNC,
            resp_type: MMC_RSP_R1,
            cmdarg,
        };
        self.hardware
            .sdmmc_do_request(&cmd, Some(&data), &mut resp, 0)?;

        // The use of fence here is actually wrong
        // As the fence(Ordering::Acquire) on arm platform
        // The cache maintenance instructions are not ordered 
        // by the Load-Acquire and Store-Release instructions
        // But I will just leave it here as I cannot figure out
        // A more elegant way and code works fine anyway
        core::sync::atomic::fence(Ordering::Acquire);

        // Error handling here
        invalidate_cache_fn();

        // Since we are using u8 here, the endianness does matter
        // 0xF indicate function switch error
        // TODO: Double check here and deliberately trigger switch error to see if the field
        // is being set to 0xF
        if unsafe { (*raw_memory)[SD_SWITCH_FUNCTION_SELECTION_GROUP_ONE] & 0xF == 0xF } {
            return Err(SdmmcError::EINVAL);
        }
        Ok(())
    }

    /// Unsafe because trying to dereference raw pointer
    unsafe fn sdcard_check_supported_speed_class(
        &mut self,
        raw_memory: *mut [u8; 64],
        invalidate_cache_fn: fn(),
        physical_memory_addr: u64,
    ) -> Result<(), SdmmcError> {
        let data: MmcData = MmcData {
            blocksize: 64,
            blockcnt: 1,
            flags: MmcDataFlag::SdmmcDataRead,
            addr: physical_memory_addr,
        };

        let mut resp: [u32; 4] = [0; 4];

        let mut card_cap: SdcardCapability = sdmmc_capability::SdcardCapability(MMC_EMPTY_CAP);
        let cmd: SdmmcCmd = SdmmcCmd {
            cmdidx: SD_CMD_SWITCH_FUNC,
            resp_type: MMC_RSP_R1,
            cmdarg: 0x00FFFFFF,
        };

        self.hardware
            .sdmmc_do_request(&cmd, Some(&data), &mut resp, 0)?;

        core::sync::atomic::fence(Ordering::Acquire);

        invalidate_cache_fn();
        // Typical speed class supported: 80 03
        match self.mmc_ios.signal_voltage {
            MmcSignalVoltage::Voltage330 => {
                let speed_class_byte: u8 = unsafe { (*raw_memory)[SD_SWITCH_FUNCTION_GROUP_ONE] };
                if speed_class_byte & SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_SDHS != 0 {
                    card_cap.insert(sdmmc_capability::SdcardCapability(MMC_TIMING_SD_HS));
                }
            }
            MmcSignalVoltage::Voltage180 => {
                let speed_class_byte: u8 = unsafe { (*raw_memory)[SD_SWITCH_FUNCTION_GROUP_ONE] };
                if speed_class_byte & SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR12 != 0 {
                    card_cap.insert(sdmmc_capability::SdcardCapability(MMC_TIMING_UHS_SDR12));
                }
                if speed_class_byte & SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR25 != 0 {
                    card_cap.insert(sdmmc_capability::SdcardCapability(MMC_TIMING_UHS_SDR25));
                }
                if speed_class_byte & SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR50 != 0 {
                    card_cap.insert(sdmmc_capability::SdcardCapability(MMC_TIMING_UHS_SDR50));
                }
                if speed_class_byte & SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_SDR104 != 0 {
                    card_cap.insert(sdmmc_capability::SdcardCapability(MMC_TIMING_UHS_SDR104));
                }
                if speed_class_byte & SD_SWITCH_FUNCTION_GROUP_ONE_CHECK_UHS_DDR50 != 0 {
                    card_cap.insert(sdmmc_capability::SdcardCapability(MMC_TIMING_UHS_DDR50));
                }
            }
            // For sdcard, the signal voltage cannot be 1.2V
            MmcSignalVoltage::Voltage120 => return Err(SdmmcError::EUNDEFINED),
        }
        // Add the card cap to self
        if let Some(MmcDevice::Sdcard(ref mut sdcard)) = &mut self.mmc_device {
            sdcard.card_cap |= card_cap;
        } else {
            return Err(SdmmcError::EINVAL);
        }
        Ok(())
    }

    /// Since we are using u8 here, the endianness does matter
    /// I should change the process of access raw memory to using volatile read
    fn tune_sdcard_performance(
        &mut self,
        memory: *mut [u8; 64],
        cache_invalidate_function: fn(),
        physical_memory_addr: u64,
    ) -> Result<(), SdmmcError> {
        let mut resp: [u32; 4] = [0; 4];

        if let Some(MmcDevice::Sdcard(ref mut sdcard)) = &mut self.mmc_device {
            let scr: Scr = unsafe {
                Sdcard::sdcard_get_configuration_register(
                    &mut self.hardware,
                    physical_memory_addr,
                    memory,
                    cache_invalidate_function,
                    sdcard.relative_card_addr,
                )?
            };

            if scr.support_set_block_count {
                sdcard.method = BlockTransmissionMode::SetBlockCount;
            }

            sdcard.card_config = Some(scr);
        }

        if self.mmc_ios.bus_width == MmcBusWidth::Width1
            && self
                .host_capability
                .contains(SdmmcHostCapability(MMC_CAP_4_BIT_DATA))
        {
            // Switch data bits per transfer
            let relative_card_address: u16;
            if let Some(MmcDevice::Sdcard(ref sdcard)) = self.mmc_device {
                relative_card_address = sdcard.relative_card_addr;
            } else {
                return Err(SdmmcError::EINVAL);
            }
            // CMD55 + ACMD6 to set the card to 4-bit mode (if supported by host and card)
            let cmd = SdmmcCmd {
                cmdidx: MMC_CMD_APP_CMD,
                resp_type: MMC_RSP_R1,
                cmdarg: (relative_card_address as u32) << 16,
            };
            self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 0)?;

            let cmd = SdmmcCmd {
                cmdidx: SD_CMD_APP_SET_BUS_WIDTH,
                resp_type: MMC_RSP_R1,
                cmdarg: 2, // Argument for 4-bit mode (0 for 1-bit mode)
            };
            self.hardware.sdmmc_do_request(&cmd, None, &mut resp, 0)?;

            self.hardware.sdmmc_config_bus_width(MmcBusWidth::Width4)?;

            debug_log!("Tuning datalanes succeed!\n");

            // If any of the cmd above fail, the card should be completely reinit
            self.mmc_ios.bus_width = MmcBusWidth::Width4;
            // TODO: Change sdcard bus width here, or get rid of that field completely
        }

        debug_log!("Checking supported speed classes\n");

        if let Some(MmcDevice::Sdcard(ref mut sdcard)) = self.mmc_device {
            match self.mmc_ios.signal_voltage {
                MmcSignalVoltage::Voltage330 => {
                    sdcard.card_state.timing = MmcTiming::Legacy;
                    if !sdcard
                        .card_cap
                        .contains(SdcardCapability(MMC_TIMING_LEGACY))
                    {
                        // When the target speed is None, the sdcard_switch_speed update sdcard speed capability
                        unsafe {
                            self.sdcard_check_supported_speed_class(
                                memory,
                                cache_invalidate_function,
                                physical_memory_addr,
                            )?;
                        }
                    }
                }
                MmcSignalVoltage::Voltage180 => {
                    sdcard.card_state.timing = MmcTiming::UhsSdr12;
                    if !sdcard
                        .card_cap
                        .contains(SdcardCapability(MMC_TIMING_UHS_SDR12))
                    {
                        unsafe {
                            self.sdcard_check_supported_speed_class(
                                memory,
                                cache_invalidate_function,
                                physical_memory_addr,
                            )?;
                        }
                    }
                }
                MmcSignalVoltage::Voltage120 => return Err(SdmmcError::EUNDEFINED),
            };
        } else {
            return Err(SdmmcError::EUNDEFINED);
        }

        let mut target_timing;
        let sdcard_cap: SdcardCapability;
        if let Some(MmcDevice::Sdcard(ref sdcard)) = self.mmc_device {
            debug_log!("Switch to higher speed class\n");
            sdcard_cap = sdcard.card_cap.clone();
            target_timing = sdcard.card_state.timing;
            // This 'tune_speed thing is a feature called labeled block in Rust
            'tune_speed: {
                match self.mmc_ios.signal_voltage {
                    MmcSignalVoltage::Voltage330 => {
                        if sdcard_cap.contains(SdcardCapability(MMC_TIMING_SD_HS))
                            && self
                                .host_capability
                                .contains(SdmmcHostCapability(MMC_TIMING_SD_HS))
                        {
                            target_timing = MmcTiming::SdHs;
                        }
                    }
                    MmcSignalVoltage::Voltage180 => {
                        if sdcard_cap.contains(SdcardCapability(MMC_TIMING_UHS_SDR104))
                            && self
                                .host_capability
                                .contains(SdmmcHostCapability(MMC_TIMING_UHS_SDR104))
                        {
                            target_timing = MmcTiming::UhsSdr104;
                            // If the switch speed succeed, terminate the block
                            break 'tune_speed;
                        }
                        if !sdcard_cap.contains(SdcardCapability(MMC_TIMING_UHS_DDR50))
                            && self
                                .host_capability
                                .contains(SdmmcHostCapability(MMC_TIMING_UHS_DDR50))
                        {
                            target_timing = MmcTiming::UhsDdr50;
                            break 'tune_speed;
                        }
                        if !sdcard_cap.contains(SdcardCapability(MMC_TIMING_UHS_SDR50))
                            && self
                                .host_capability
                                .contains(SdmmcHostCapability(MMC_TIMING_UHS_SDR50))
                        {
                            target_timing = MmcTiming::UhsSdr50;
                            break 'tune_speed;
                        }
                        if !sdcard_cap.contains(SdcardCapability(MMC_TIMING_UHS_SDR25))
                            && self
                                .host_capability
                                .contains(SdmmcHostCapability(MMC_TIMING_UHS_SDR25))
                        {
                            target_timing = MmcTiming::UhsSdr25;
                            break 'tune_speed;
                        }
                    }
                    MmcSignalVoltage::Voltage120 => return Err(SdmmcError::EUNDEFINED),
                }
            };
            unsafe {
                self.sdcard_switch_speed(
                    target_timing,
                    memory,
                    cache_invalidate_function,
                    physical_memory_addr,
                )?;
            }
            self.mmc_ios.clock = self.hardware.sdmmc_config_timing(target_timing)?;

            self.hardware
                .sdmmc_execute_tuning(physical_memory_addr as *mut [u8; 64])?;

            debug_log!("Current frequency: {}Hz\n", self.mmc_ios.clock);
        } else {
            return Err(SdmmcError::EUNDEFINED);
        }
        if let Some(MmcDevice::Sdcard(ref mut sdcard)) = self.mmc_device {
            sdcard.card_state.timing = target_timing;
        }

        Ok(())
    }

    pub fn config_interrupt(
        &mut self,
        enable_irq: bool,
        enable_sdio_irq: bool,
    ) -> Result<(), SdmmcError> {
        self.mmc_ios.enabled_irq = enable_irq | enable_sdio_irq;
        self.hardware
            .sdmmc_config_interrupt(enable_irq, enable_sdio_irq)
    }

    pub fn ack_interrupt(&mut self) -> Result<(), SdmmcError> {
        self.hardware.sdmmc_ack_interrupt()
    }

    pub async fn read_block(
        mut self,
        blockcnt: u32,
        start_idx: u64,
        destination: u64,
    ) -> (Result<(), SdmmcError>, SdmmcProtocol<T>) {
        let trans_meth: BlockTransmissionMode = {
            if let Some(ref device) = self.mmc_device {
                match device {
                    MmcDevice::Sdcard(sdcard) => sdcard.method.clone(),
                    MmcDevice::EMmc(emmc) => emmc.method.clone(),
                    MmcDevice::Unknown => return (Err(SdmmcError::EUNSUPPORTEDCARD), self),
                }
            } else {
                return (Err(SdmmcError::ENOCARD), self);
            }
        };

        let mut cmd: SdmmcCmd;
        let mut res: Result<(), SdmmcError>;
        let mut turing: bool = false;

        // TODO: Figure out a way to support cards with 4 KB sector size
        let data: MmcData = MmcData {
            blocksize: 512,
            blockcnt,
            flags: MmcDataFlag::SdmmcDataRead,
            addr: destination,
        };
        let mut resp: [u32; 4] = [0; 4];

        // TODO: Add more validation check in the future
        // Like sdmmc card usually cannot transfer arbitrary number of blocks at once

        // The cmd arg for read operation is different between some card variation as showed by uboot code below
        /*
            if (mmc->high_capacity)
                cmd.cmdarg = start;
            else
                cmd.cmdarg = start * mmc->read_bl_len;
        */
        // For now we default to assume the card is high_capacity
        // TODO: Fix it when we properly implement card boot up
        // TODO: If we boot the card by ourself or reset the card, remember to send block len cmd
        loop {
            if blockcnt == 1 {
                cmd = SdmmcCmd {
                    cmdidx: MMC_CMD_READ_SINGLE_BLOCK,
                    resp_type: MMC_RSP_R1,
                    cmdarg: start_idx as u32,
                };
                res = Self::sdmmc_async_request(&mut self.hardware, &cmd, Some(&data), &mut resp)
                    .await;
            } else {
                // TODO: Add if here to determine if the card support cmd23 or not to determine to use cmd23 or cmd12
                // Set the expected number of blocks

                cmd = SdmmcCmd {
                    cmdidx: MMC_CMD_READ_MULTIPLE_BLOCK,
                    resp_type: MMC_RSP_R1,
                    cmdarg: start_idx as u32,
                };

                res = Self::sdmmc_multi_blocks_io(
                    &mut self.hardware,
                    &cmd,
                    &data,
                    &mut resp,
                    trans_meth.clone(),
                )
                .await;
            }
            match res {
                Ok(()) => {}
                Err(ref err) => {
                    let stop_cmd: SdmmcCmd = SdmmcCmd {
                        cmdidx: MMC_CMD_STOP_TRANSMISSION,
                        resp_type: MMC_RSP_R1B,
                        cmdarg: 0,
                    };
                    // Sending stop command manually regardless of whether it has been sent or not
                    let _ =
                        Self::sdmmc_async_request(&mut self.hardware, &stop_cmd, None, &mut resp)
                            .await;

                    if let SdmmcError::EIO = err {
                        if let Some(memory) = self.private_memory {
                            if turing == false {
                                turing = true;
                                if let Ok(()) = self.hardware.sdmmc_execute_tuning(memory) {
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            break;
        }
        (res, self)
    }

    // Almost the same with read_block aside from the cmd being sent is a bit different
    // For any future code add to read_block/write_block, remember to change both
    // Should read_block/write_block be the same function?
    pub async fn write_block(
        mut self,
        blockcnt: u32,
        start_idx: u64,
        source: u64,
    ) -> (Result<(), SdmmcError>, SdmmcProtocol<T>) {
        let trans_meth: BlockTransmissionMode = {
            if let Some(ref device) = self.mmc_device {
                match device {
                    MmcDevice::Sdcard(sdcard) => sdcard.method.clone(),
                    MmcDevice::EMmc(emmc) => emmc.method.clone(),
                    MmcDevice::Unknown => return (Err(SdmmcError::EUNSUPPORTEDCARD), self),
                }
            } else {
                return (Err(SdmmcError::ENOCARD), self);
            }
        };

        let cmd: SdmmcCmd;
        let res: Result<(), SdmmcError>;
        // TODO: Figure out a way to support cards with 4 KB sector size
        let data: MmcData = MmcData {
            blocksize: 512,
            blockcnt,
            flags: MmcDataFlag::SdmmcDataWrite,
            addr: source,
        };
        let mut resp: [u32; 4] = [0; 4];
        // TODO: Add more validation check in the future

        if blockcnt == 1 {
            cmd = SdmmcCmd {
                cmdidx: MMC_CMD_WRITE_SINGLE_BLOCK,
                resp_type: MMC_RSP_R1,
                cmdarg: start_idx as u32,
            };
            res = Self::sdmmc_async_request(&mut self.hardware, &cmd, Some(&data), &mut resp).await;

            return (res, self);
        } else {
            // TODO: Add if here to determine if the card support cmd23 or not to determine to use cmd23 or cmd12
            // Set the expected number of blocks

            cmd = SdmmcCmd {
                cmdidx: MMC_CMD_WRITE_MULTIPLE_BLOCK,
                resp_type: MMC_RSP_R1,
                cmdarg: start_idx as u32,
            };

            res =
                Self::sdmmc_multi_blocks_io(&mut self.hardware, &cmd, &data, &mut resp, trans_meth)
                    .await;

            match res {
                Ok(()) => {}
                Err(_) => {
                    let cmd: SdmmcCmd = SdmmcCmd {
                        cmdidx: MMC_CMD_STOP_TRANSMISSION,
                        resp_type: MMC_RSP_R1B,
                        cmdarg: 0,
                    };
                    // Sending stop command manually regardless of whether it has been sent or not
                    let _ =
                        Self::sdmmc_async_request(&mut self.hardware, &cmd, None, &mut resp).await;
                }
            }

            return (res, self);
        }
    }

    // TODO: correct erase block alignment, error handling and sdcard internal erasure timing(this erasure seems to be non-blocking?)
    // It is likely(from reading Linux source code), polling in some host controller could be necessary
    pub async fn erase_block(
        mut self,
        start_idx: u64,
        end_idx: u64,
    ) -> (Result<(), SdmmcError>, SdmmcProtocol<T>) {
        let mut cmd: SdmmcCmd;
        let mut res: Result<(), SdmmcError>;

        let mut resp: [u32; 4] = [0; 4];

        cmd = SdmmcCmd {
            cmdidx: SD_CMD_ERASE_WR_BLK_START,
            resp_type: MMC_RSP_R1,
            cmdarg: start_idx as u32,
        };

        res = Self::sdmmc_async_request(&mut self.hardware, &cmd, None, &mut resp).await;

        if let Err(_) = res {
            return (res, self);
        }

        cmd = SdmmcCmd {
            cmdidx: SD_CMD_ERASE_WR_BLK_END,
            resp_type: MMC_RSP_R1,
            cmdarg: end_idx as u32,
        };

        res = Self::sdmmc_async_request(&mut self.hardware, &cmd, None, &mut resp).await;

        if let Err(_) = res {
            return (res, self);
        }

        cmd = SdmmcCmd {
            cmdidx: MMC_CMD_ERASE,
            resp_type: MMC_RSP_R1B,
            cmdarg: SD_ERASE_ARG,
        };

        res = Self::sdmmc_async_request(&mut self.hardware, &cmd, None, &mut resp).await;

        return (res, self);
    }

    /// Function to execute one sdmmc request asynchronously
    /// The resp could be used for future error parsing
    async fn sdmmc_async_request(
        hardware: &mut T,
        cmd: &SdmmcCmd,
        data: Option<&MmcData>,
        resp: &mut [u32; 4],
    ) -> Result<(), SdmmcError> {
        // Send the command to the host sdcard
        hardware.sdmmc_send_command(cmd, data)?;
        // Wait until sdcard return the result to the driver
        let res: Result<(), SdmmcError> = SdmmcCmdFuture::new(hardware, cmd, resp).await;
        // Acknowledge interrupts
        hardware.sdmmc_ack_interrupt()?;

        res
    }

    /// Change this function so that if a request report back error
    /// MMC_CMD_STOP_TRANSMISSION must be sent in the end so the card
    /// stop transmission correctly
    async fn sdmmc_multi_blocks_io(
        hardware: &mut T,
        request_cmd: &SdmmcCmd,
        data: &MmcData,
        resp: &mut [u32; 4],
        transmission_mode: BlockTransmissionMode,
    ) -> Result<(), SdmmcError> {
        // Trasmission stage
        match transmission_mode {
            BlockTransmissionMode::SetBlockCount => {
                let cmd: SdmmcCmd = SdmmcCmd {
                    cmdidx: MMC_CMD_SET_BLOCK_COUNT,
                    resp_type: MMC_RSP_R1,
                    cmdarg: data.blockcnt, // block count for the upcoming CMD25 operation
                };

                Self::sdmmc_async_request(hardware, &cmd, None, resp).await?;

                Self::sdmmc_async_request(hardware, &request_cmd, Some(&data), resp).await
            }
            BlockTransmissionMode::StopTransmission => {
                let temp_res: Result<(), SdmmcError> =
                    Self::sdmmc_async_request(hardware, &request_cmd, Some(&data), resp).await;

                // Uboot code for determine response type in this case
                // cmd.resp_type = (IS_SD(mmc) || write) ? MMC_RSP_R1b : MMC_RSP_R1;
                // TODO: Add mmc checks here
                let cmd: SdmmcCmd = SdmmcCmd {
                    cmdidx: MMC_CMD_STOP_TRANSMISSION,
                    resp_type: MMC_RSP_R1B,
                    cmdarg: 0,
                };

                // Technically this command has very little possibility to fail
                // Unless for hardware or environment issue
                let _ = Self::sdmmc_async_request(hardware, &cmd, None, resp).await;

                temp_res
            }
            BlockTransmissionMode::AutoStop => {
                Self::sdmmc_async_request(hardware, &request_cmd, Some(&data), resp).await
            }
        }
    }
}
enum CmdState {
    // Waiting for the response
    WaitingForResponse,
    // Finished
    Finished,
}

pub struct SdmmcCmdFuture<'a, 'b, 'c> {
    hardware: &'a mut dyn SdmmcHardware,
    cmd: &'b SdmmcCmd,
    waker: Option<Waker>,
    state: CmdState,
    response: &'c mut [u32; 4],
}

impl<'a, 'b, 'c> SdmmcCmdFuture<'a, 'b, 'c> {
    pub fn new(
        hardware: &'a mut dyn SdmmcHardware,
        cmd: &'b SdmmcCmd,
        response: &'c mut [u32; 4],
    ) -> SdmmcCmdFuture<'a, 'b, 'c> {
        SdmmcCmdFuture {
            hardware,
            cmd,
            waker: None,
            state: CmdState::WaitingForResponse,
            response,
        }
    }
}

/// SdmmcCmdFuture serves as the basic building block for async fn above
/// In the context of Sdmmc device, since the requests are executed linearly under the hood
/// We actually do not need an executor to execute the request
/// The context can be ignored unless someone insist to use an executor for the requests
/// So for now, the context is being stored in waker but this waker will not be used
impl<'a, 'b, 'c> Future for SdmmcCmdFuture<'a, 'b, 'c> {
    type Output = Result<(), SdmmcError>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // As I have said above, this waker is not being used so it do not need to be shared data
        // But store the waker provided anyway
        // Beware you need to update waker every polling, for more details about why
        // read Asynchronous Programming in Rust
        self.waker = Some(cx.waker().clone());

        match self.state {
            CmdState::WaitingForResponse => {
                let res: Result<(), SdmmcError>;
                {
                    let this: &mut SdmmcCmdFuture<'a, 'b, 'c> = self.as_mut().get_mut();
                    let cmd: &SdmmcCmd = this.cmd;
                    let response: &mut [u32; 4] = this.response;
                    let hardware: &dyn SdmmcHardware = this.hardware;
                    res = hardware.sdmmc_receive_response(cmd, response);
                }
                if let Err(SdmmcError::EBUSY) = res {
                    return Poll::Pending;
                } else {
                    self.state = CmdState::Finished;
                    return Poll::Ready(res);
                }
            }
            // Despite the status is ready, the state machine get polled again
            CmdState::Finished => return Poll::Ready(Err(SdmmcError::EUNDEFINED)),
        }
    }
}

/// Helper function to print out the content of one block
#[allow(dead_code)]
unsafe fn print_one_block(ptr: *const u8, num: usize) {
    unsafe {
        // Iterate over the number of bytes and print each one in hexadecimal format
        for i in 0..num {
            let byte = *ptr.add(i);
            if i % 16 == 0 {
                debug_log!("\n{:04x}: ", i);
            }
            debug_log!("{:02x} ", byte);
        }
        debug_log!("\n");
    }
}
