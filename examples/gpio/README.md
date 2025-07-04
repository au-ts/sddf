<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Gpio example

We have 2 GPIOs:
- GPIO_1 is set to output and should be attached to an LED then Ground.
- GPIO_2 is set to input and should be attached a button then to 3.3V.
When you push the button it should alternate the current state of the LED (off or on).

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

When running the example, you should see something similar to the following
output if USE_POLLING = 0:
```
CLIENT|INFO: Turned off!
CLIENT|INFO: Waiting for IRQ from driver!
```

Press the button.
Light should turn on.

```
CLIENT|INFO: Turned on!
CLIENT|INFO: Waiting for IRQ from driver!
```

When running the example, you should see something similar to the following
output if USE_POLLING = 1:
```
CLIENT|INFO: Turned off!
```

Press the button.
Light should turn on.

```
CLIENT|INFO: Turned on!
```
