#![no_std] // Don't link the standard library

use core::hint;

/// Api should only accessible in this crate
#[doc(hidden)]
pub use sel4_microkit::debug_print;

/// Spins for an approximate number of nanoseconds.
///
/// This function is unreliable because it does not account for CPU frequency,
/// power-saving modes, or other hardware variations. It should be used only
/// in situations where approximate delays are sufficient.
///
/// # Arguments
///
/// * `time_ns` - The approximate number of nanoseconds to spin-wait.
///
/// # Notes
///
/// This function uses a simple busy-wait loop combined with `hint::spin_loop`
/// to reduce contention during the wait. The actual delay may vary significantly
/// depending on the hardware and system load.
///
/// For accurate delays, use a hardware timer or platform-specific APIs.
/// TODO: Change this to using a timer to stop later
#[inline]
pub fn process_wait_unreliable(time_ns: u64) {
    for _ in 0..time_ns {
        hint::spin_loop(); // Use spin loop hint to reduce contention during the wait
    }
}

/// `sel4-microkit` specific serial implementation
#[macro_export]
macro_rules! debug_log {
    ($($arg:tt)*) => {
        $crate::debug_print!($($arg)*);
    }
}
