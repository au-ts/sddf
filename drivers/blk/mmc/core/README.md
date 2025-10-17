<!--
    Copyright 2025, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->
**Note:** This driver is in the early stages of development and does not yet implement the full feature set found in mature stacks like the Linux MMC subsystem.

---

## Features

### Supported
- **Card Types:** SDHC / SDXC
- **Bus Speeds:** High Speed (SDHS) / UHS-I
- **Core Operations:** Asynchronous Read, Write, and Erase

### Not Yet Implemented or Tested
- **Card Types:** SDSC / SDUC, eMMC
- **Interface Modes:** SPI mode
- **Bus Speeds:** Speed classes higher than UHS-I (e.g., UHS-II, UHS-III)
- A comprehensive set of features found in mature MMC stacks.

---

## Hardware Platform Support

| Platform       | Status          |
| :------------- | :-------------- |
| Odroid C4      | ✅ Supported    |
| sdhci-zynqmp   | 🚧 In Progress  |

---

## Adding Support for a New Hardware Platform

Porting the driver to a new hardware platform involves implementing the hardware-specific logic. Follow these steps:

1.  **Familiarize Yourself:** Study the driver's architecture and review the reference implementation for the Odroid C4 to understand the core components.
2.  **Implement the HAL:** Create a new hardware abstraction layer (HAL) for your platform by implementing the `SdmmcHardware` trait. This trait defines the interface for all hardware-specific operations.
3.  **Build with Logging:** Compile your HAL and the core protocol crate with the `dev-logs` feature enabled to get detailed diagnostic output.
4.  **Test and Verify:** Run the driver on your hardware. Analyze the logs to verify that the initialization sequence and command responses are correct.