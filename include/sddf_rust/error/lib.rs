#![no_std] // Don't link the standard library

#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub enum MicrokitError {
    EINVAL = 0,
}
