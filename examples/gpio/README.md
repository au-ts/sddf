<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Gpio example

We have 3 GPIOs:
- GPIO_1 is set to output and should be attached to resistors then an LED then Ground.
- GPIO_2 is set to input and should start unattached to anything. Note for this example this pin should have a floating logical state of 0 or a pull down resistor attached.
- GPIO_3 is set to output should start unattached to anythng.

When you connect GPIO_2 and GPIO_3 together the LED should light up.
When you disconnect GPIO_2 and GPIO_3 the LED should turn off.

There is also 2 testing modes, one for polling and for for IRQ based

## Building

The following platforms are supported:
* maaxboard
* odroidc4 (work in progress)

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board>
```

After building, the system image to load will be `build/loader.img`.

### Zig

You can also build this example with the Zig build system:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=<board>
```

The final bootable image will be in `zig-out/bin/loader.img`.

## Running

NOTE: both ways emulate a BOTH EDGE driven model of changing the LED.
Do #define USE_POLLING to use Polling mode, otherwise will default to irq based. 

Since there is no debounce logic it may appear to not work with the irq based loop.

Make sure you chose pins that are actually set as GPIO's via the pinmux.

Make sure you have actually checked which pins mapped to which physical pins (the brought out pins).

## Warning
For Meson the i2c pins have external pull up resistors.
