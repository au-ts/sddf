<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Timer example

This is a very simple example where a single client program is setting
timeouts and getting the current time from a timer driver.

## Building

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board>
```

Currently the options for `MICROKIT_BOARD` are:
* odroidc4
* qemu_virt_aarch64

After building, the system image to load will be `build/loader.img`.

If you wish to simulate on the QEMU virt AArch64 platform, you can append `qemu` to your make command
after building for qemu_virt_aarch64.

### Zig

You can also build this example with the Zig build system:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=<board>
```

The options for `<board>` are the same as the Makefile.

You can simulate QEMU with:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=qemu_virt_aarch64 qemu
```

The final bootable image will be in `zig-out/bin/loader.img`.

## Running

When running the example, you should see something similar to the following
output:
```
CLIENT|INFO: The time now is: 29422640
CLIENT|INFO: Setting a time out for 1 second
CLIENT|INFO: Got a timeout!
CLIENT|INFO: Now the time (in nanoseconds) is: 1031980992
CLIENT|INFO: Got a timeout!
CLIENT|INFO: Now the time (in nanoseconds) is: 2032392176
CLIENT|INFO: Got a timeout!
CLIENT|INFO: Now the time (in nanoseconds) is: 3032782448
CLIENT|INFO: Got a timeout!
CLIENT|INFO: Now the time (in nanoseconds) is: 4033253600
CLIENT|INFO: Got a timeout!
CLIENT|INFO: Now the time (in nanoseconds) is: 5033766064
CLIENT|INFO: Got a timeout!
CLIENT|INFO: Now the time (in nanoseconds) is: 6034408576
```

The client will continuously set timeouts and read the current time.
