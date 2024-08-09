<!--
    Copyright 2024, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Block (mmc) client example

This is an example to show a single client reading & writing from an SD card.

It has been developed on an Avnet MaaXBoard. It has been tested on both the MaaXBoard and NXP i.MX8MM-EVK platforms.

The client reads & writes to the 3rd partition on the SD card (0-index = 2).
It _will_ overwrite data in this partition.

The example has been tested using a Class 4 SanDisk 8GiB microSD card formatted with the [Debian Linux Out of Box Image](https://downloads.element14.com/downloads/zedboard/MaaxBoard/maaxboard/02LinuxShipmentImage_Debian.zip), with an additional partition created in the free space following the Linux rootfs.

## Building
### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board> MICROKIT_CONFIG=<debug/release>
```

Currently the options for `MICROKIT_BOARD` are:

* maaxboard
* imx8mm_evk

## Running

The produced `build/loader.img` can then be loaded from U-Boot.

It should produce the following output:

```
Hello from client
client notified!
client notified!
client notified!
client notified!
client notified!
[   0] = 0x3
[   1] = 0x4
[   2] = 0x5
[   3] = 0x6
[ 508] = 0xff
[ 509] = 0x0
[ 510] = 0x1
[ 511] = 0x2
[ 512] = 0x3
[ 513] = 0x4
[ 514] = 0x5
[ 515] = 0x6
[ 516] = 0x7
[4092] = 0xff
[4093] = 0x0
[4094] = 0x1
[4095] = 0x2
[4096] = 0x3
[4097] = 0x4
[NW-3] = 0x0
[NW-2] = 0x1
[NWB-] = 0x2

[NWB=] = 0x0
[NWB+] = 0x0
[NW++] = 0x0
[NR-2] = 0x0
[NR-1] = 0x0

[NRB=] = 0x3
[NR+1] = 0x4
[NR+2] = 0x5
[NR+3] = 0x6
Client read/write data is correct!
```

The client first zeroes the SD card, then writes some data and reads it back.
From `0` to `NWB-`, the bytes should be an increasing sequence starting at 0x3 and wrapping around repeatedly. These are read from the SD card.
From `NWB=` to `NR-1`, these bytes should all be zero, also read from the SD card.
From `NRB=` onwards, these bytes are set up for writing _from_ host to the _sd card_, and should not have been overwritten during reads.
