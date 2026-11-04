<!--
    Copyright 2026, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# USB example

This is a simple example demonstrating keyboard, mice and mass-storage device
support via USB. There are two virtualisers: one for human-interface devices and
one for mass-storage devices. The first device of each type that is connected
will be bound to its respective virtualiser until it is disconnected. 

## Building

The following platforms are supported:

* rpi4b_1gb[^1]

[^1]: While the Raspberry Pi 4B is supported, it requires activating a legacy
USB controller via a device-tree overlay and non-USB-C power delivery (the USB-C
port is the only port supported by the legacy controller). The Raspberry Pi
Compute Module 4 is almost equivalent, and when paired with its I/O board,
is a much more convenient platform.

### Make

(More detailed build instructions are to come.)

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board>
```

After building, the system image to load will be `build/loader.img`.

## Running

When running the example, you should see something similar to the following
output:
```
CLIENT|INFO: Starting...
CLIENT|INFO: A mass storage device has been mounted
    Kingston DataTraveler 3.0 rev 
    Disk size: 59006 MB
    Block count: 120845300; Block size: 512
CLIENT|INFO: A keyboard device has been mounted
CLIENT|INFO: Keyboard HID report received
    Modifiers:  0x02     <LeftShift> 
    Keycode:    0x0b    H
CLIENT|INFO: i
CLIENT|INFO: t
CLIENT|INFO: Keyboard HID report received
    Modifiers:  0x01     <LeftControl> 
    Keycode:    0x17    t
CLIENT|INFO: A keyboard device has been unmounted
CLIENT|INFO: A mouse device has been mounted
CLIENT|INFO: Mouse HID report received
    Buttons:    0x01     <ButtonLeft> 
    X offset:   0
    Y offset:   0
```
