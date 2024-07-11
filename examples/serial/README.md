<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Serial example

This is a serial subsystem example demonstrating two receive and transmit clients.

## Building

The following platforms are supported:
* cheshire
* imx8mm_evk
* imx8mp_evk
* imx8mq_evk
* maaxboard
* odroidc2
* odroidc4
* qemu_virt_aarch64
* qemu_virt_riscv64
* star64
* zcu102

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board> MICROKIT_CONFIG=<debug/release/benchmark>
```

After building, the system image to load will be `build/loader.img`.

If you wish to simulate on one of the QEMU platforms (qemu_virt_aarch64 or qemu_virt_riscv64),
you can append `qemu` to your make command to start QEMU after everything compiles.

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

## Running/Using

When running the example in debug mode you should see the following output from the serial transmit
virtualiser upon booting, showing which client is associated with which colour:
```sh
Begin input
'client0' is client 0
'client1' is client 1
```

This will be followed by initialisation output from each of the serial clients printed in their
respective colour:
```sh
Hello world! I am client1.
Please give me character!
Hello world! I am client0.
Please give me character!
```

When typing in characters into your terminal, they will by default be directed to client 0. Upon
receiving a character, client 0 will echo it. After receiving 10 characters, client 0 will print:
```sh
client0 has received 10 characters so far!
```

Client 1 is a clone of client 0, and will behave the same way. To switch clients, enter:
```sh
CTRL + \, <client number>, \r
```

For example, to switch to client 1, enter:
```sh
CTRL + \, 1, \r
```

If in debug mode, you should see the following output when doing so:
```sh
VIRT_RX|LOG: switching to client 1
```

## Description

The serial example system contains two clients which are both able to transmit and receive
characters over serial. The clients are based on the same executable generated from
`examples/serial/client.c`.

Each serial client demonstrates two methods of outputting to serial: the first uses `sddf_printf`
(linked with `_sddf_putchar` defined in `util/putchar_serial.c`), and the second uses
`sddf_putchar_unbuffered` defined in the same file.

The first method demonstrates character buffering before output to the transmit virtualiser based on
a flush character or queue capacity, the second demonstrates characters being transmitted in an
unbuffered fashion, typically used by a REPL.

Each serial client sits in an event loop, awaiting notification from the receive virtualiser.
When a notification is received, the client outputs the character in an unbuffered fashion. Every 10
characters the client prints a message in a buffered fashion.

In this example, `enable_color` is set to `True` (which is on by default when creating a serial
subsystem using a Python metaprogram) so each client prints with a different colour.

## Documentation

Further documentation for the serial subsystem can be found in the [developer docs](/docs/serial/serial.md).
