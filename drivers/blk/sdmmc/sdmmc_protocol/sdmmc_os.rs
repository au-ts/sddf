use crate::sdmmc::MmcPowerMode;
use crate::sdmmc::MmcSignalVoltage;
use crate::sdmmc::SdmmcError;
use core::sync::atomic::AtomicU8;
use core::sync::atomic::Ordering;

pub trait Sleep {
    /// For putting the process to sleep for a while,
    /// The default spinning implementation is a very unreliable way to put the process to sleep
    fn usleep(&mut self, time_us: u32) {
        let time_ns: u64 = time_us as u64 * 1000;
        for _ in 0..time_ns {
            core::hint::spin_loop(); // Use spin loop hint to reduce contention during the wait
        }
    }
}

pub trait VoltageOps {
    fn card_voltage_switch(&mut self, voltage: MmcSignalVoltage) -> Result<(), SdmmcError> {
        core::panic!("Voltage switch not implemented!");
    }

    fn card_set_power(&mut self, power_mode: MmcPowerMode) -> Result<(), SdmmcError> {
        core::panic!("Power cycling not implemented!");
    }
}

pub fn process_wait_unreliable(time_ns: u64) {
    for _ in 0..time_ns {
        core::hint::spin_loop(); // Use spin loop hint to reduce contention during the wait
    }
}

pub trait Log {
    fn log(&self, args: core::fmt::Arguments) {
        core::panic!("Logging not implemented!");
    }
}

const UNINITIALIZED: u8 = 0;
const INITIALIZING: u8 = 1;
const INITIALIZED: u8 = 2;
static LOGGER_STATE: AtomicU8 = AtomicU8::new(UNINITIALIZED);
static mut LOGGER: Option<&'static dyn Log> = None;

/// Why it is unsafe: A trait object of Log should provide a thread safe implementation of Log object
/// The crate treat the log function provided as a THREAD SAFE object!
pub unsafe fn set_logger(logger: &'static dyn Log) -> Result<(), ()> {
    // 1. Try to acquire the "write lock".
    // Try to change `UNINITIALIZED` to `INITIALIZING`. If it was not `UNINITIALIZED`, another thread is setting it.
    if LOGGER_STATE
        .compare_exchange(
            UNINITIALIZED,
            INITIALIZING,
            Ordering::Relaxed,
            Ordering::Relaxed,
        )
        .is_ok()
    {
        // 2. Write to the non-atomic static mut.
        // This is the operation we need to protect.
        unsafe {
            LOGGER = Some(logger);
        }

        // Signal that the data is ready.
        // We use Release ordering here. This is the crucial part!
        LOGGER_STATE.store(INITIALIZED, Ordering::Release);
        return Ok(());
    }

    Err(())
}

#[doc(hidden)]
pub fn __logging_helper(args: core::fmt::Arguments) {
    // 1. Check if the logger is initialized.
    // We use Acquire ordering here. This pairs with the `Release` store above.
    unsafe {
        if LOGGER_STATE.load(Ordering::Acquire) == INITIALIZED {
            if let Some(logger) = LOGGER {
                logger.log(args);
            }
        }
    }
}

#[macro_export]
macro_rules! print_info {
    ($($arg:tt)*) => {
        $crate::sdmmc_os::__logging_helper(format_args!($($arg)*));
    }
}

#[macro_export]
macro_rules! info {
    ($($arg:tt)*) => {
        $crate::print_info!("{}\n", format_args!($($arg)*));
    }
}

#[cfg(not(feature = "dev-logs"))]
#[macro_export]
macro_rules! dev_log {
    ($($arg:tt)*) => {};
}

#[cfg(feature = "dev-logs")]
#[macro_export]
macro_rules! dev_log {
    ($($arg:tt)*) => {
        $crate::sdmmc_os::__logging_helper(format_args!($($arg)*));
    }
}
