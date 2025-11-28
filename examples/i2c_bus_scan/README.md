<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# I<sup>2</sup>C Bus scan example

This example implements an I2C bus scanner for any device using 7-bit addressing.

## Building

### Make

To build the image, run the following command:
```sh
make MICROKIT_SDK=/path/to/sdk
```

The final bootable image will be in `build/loader.img`.

### Zig

You can also build this example with the Zig build system:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=odroidc4
```

The final bootable image will be in `zig-out/bin/loader.img`.
