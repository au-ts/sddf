#[cfg(feature = "sel4-microkit")]
pub use sel4_microkit_support::process_wait_unreliable;

#[cfg(feature = "sel4-microkit")]
pub use sel4_microkit_support::debug_log;

#[cfg(not(feature = "sel4-microkit"))]
#[inline]
pub fn process_wait_unreliable(time_ns: u64) {
    for _ in 0..time_ns {
        hint::spin_loop(); // Use spin loop hint to reduce contention during the wait
    }
}

/// Bare metal
#[cfg(not(feature = "sel4-microkit"))]
#[macro_export]
// No operation, would be optimized out
macro_rules! debug_log {
    ($($arg:tt)*) => {};
}
