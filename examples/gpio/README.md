<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# GPIO example

This example makes use two circuits.

Each GPIO outputs 3.3V.

### Circuit 1:

GPIO_H --------|>|----[R]-------- GND
             LED(2V)

Note: Add appropriate resistance.

### Circuit 2:

GPIO_X ----[ ]---- VCC (3.3)
          Button

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

# TODO

# what im trying to do with registers

# i think the best design is to make the offset in the mappings a complete calc
offset = (uint32_t)*gpio_mem + GPIO_MEM_OFFSET + AO_RTI_PULL_UP_EN_REG * 4
then call a fcuntion that returns this final address, and stores it in a pointer whhcih is the variable at that address

# TIDY UP?
- need to fix the config file and link it appropriately (apparently need a source file and header)
- get this stupid intialiser list crap sorted

- general style stuff perhaps

could just store the actual pointer in the ds
