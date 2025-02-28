# Generic Rust-Based SDMMC Driver

This repository contains a modular SDMMC driver written entirely in Rust, focusing on **async support**, **memory safety**, and **functional correctness**. While developed for LionsOS, the driver is designed to be **OS-agnostic** and extensible for other operating systems.

I’m excited to share this driver as a unique contribution to the open-source community. It combines wide compatibility, high performance, and Rust’s safety benefits, making it a standout in its category.

---

## Features

- **Modular Design**: Inspired by U-Boot and Linux, separates device-specific logic from protocol implementation, ensuring flexibility and extensibility.
- **Wide Compatibility and High Performance**:
  - Supports a range of SD cards, including **SDHC** and **SDXC**, with speed classes up to **UHS-I**.
  - While Linux only added support for UHS-II in October 2024, this driver provides robust UHS-I support, ideal for embedded systems and platforms where UHS-II adoption remains limited.
- **Memory Safety**: Utilizes Rust's strict compile-time checks and ownership model, ensuring better safety and readability compared to traditional C-based drivers.
- **OS-Agnostic**: Designed to integrate seamlessly with LionsOS but easily portable to other operating systems.

---

## Supported Hardware Platforms

- **Odroid C4**: Currently, the driver supports and has been tested on the Odroid C4 platform.
- **Adding Support**: Thanks to the modular design, adding support for additional platforms is straightforward by implementing the hardware abstraction layer for the new platform.

---

## Current Status

The driver is currently in the **final stages of development for its first iteration**:
- Core functionality has been fully implemented.
- Performance is comparable to Linux's SDMMC subsystem, with support for speed classes up to **UHS-I**.
- Code refinements and documentation updates are ongoing.
- **Expected Milestone**: Public release and merging into LionsOS main branch by February 2025.

---

## Driver Structure

The driver is organized into the following components:

1. **`sdmmc_hal` Folder**:
   - Contains the hardware abstraction layer for different platforms.
   - To add support for a new platform, implement the necessary hardware-specific interfaces here.

2. **`sdmmc_protocol` Folder**:
   - Implements the SD card protocol using the hardware abstraction layer.
   - Modify this layer to add new protocol features (e.g., hotplugging or eMMC support).

3. **`optional_os_support` Folder**:
   - Provides OS-specific utilities such as optimized wait/sleep operations(instead of spinning waiting) or printing debug messages to the terminal.
   - Modify this layer to provide support for a new OS

---

## Usage and Examples

Usage instructions and examples will be added soon. Stay tuned!

---

## Why Rust?

Rust provides unmatched safety and performance benefits for driver development:
- **Memory Safety**: Prevents common bugs like null pointer dereferences and buffer overflows.
- **Async Support**: Enables efficient, non-blocking I/O operations.
- **Readable and Extensible**: Rust’s modern syntax and tooling make the driver easier to understand and maintain compared to traditional C-based implementations.

---

## Future Plans

- Expand hardware support to additional platforms.
- Add support for legacy SDSC cards and the latest SDUC cards (though they may have limited use cases).
- Add hotplugging and eMMC support.
- Publish detailed usage examples and benchmarks.

---

## Contributing

Contributions are welcome! Feel free to open issues or submit pull requests to improve functionality, expand platform support, or enhance documentation.

---

## License

The license for this work will be added upon the first public release. The project is developed as part of my work at Trustworthy Systems, UNSW, so the copyright may reside with the university. Clarifications about licensing are ongoing.

---

## Related Links

- [LionsOS GitHub Repository](https://github.com/au-ts/lionsos)
