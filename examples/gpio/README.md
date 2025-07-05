<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Gpio example

We have 2 GPIOs:
- GPIO_1 is set to output and should be attached to an LED then Ground.
- GPIO_2 is set to input and should be attached a button then to 3.3V.
When you push the button it should alternate the current state of the LED (off or on).

The example will not work unless theres an external pull down resistor or
change the code to set an internal pull down resistor.

It may also work if floats at a low enough value.

There is also 2 modes, one for polling and for for IRQ based

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

--

When running the example, you should see something similar to the following
output if USE_POLLING is not defined:
```
CLIENT|INFO: Turned off!
CLIENT|INFO: Waiting for IRQ from driver!
```

Press + HOLD the button.
Light should turn on.

```
CLIENT|INFO: Turned on!
CLIENT|INFO: Waiting for IRQ from driver!
```

Release the button.
Light should turn off.

```
CLIENT|INFO: Turned off!
CLIENT|INFO: Waiting for IRQ from driver!
```

--

When running the example, you should see something similar to the following
output if USE_POLLING is defined:
```
CLIENT|INFO: Turned off!
```

Press + HOLD the button.
Light should turn on.

```
CLIENT|INFO: Turned on!
```

Release the button.
Light should turn off.

```
CLIENT|INFO: Turned off!
```

## Warning
For Meson the i2c pins have external pull up resistors.




