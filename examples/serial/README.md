# Serial example

This is an example to show multiple clients being used with a UART driver.

## Building

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board> MICROKIT_CONFIG=<debug/release/benchmark>
```

Currently the options for `MICROKIT_BOARD` are:
* odroidc4
* imx8mm_evk
* maaxboard
* qemu_arm_virt

After building, the system image to load will be `build/loader.img`.

If you wish to simulate on the QEMU ARM virt platform, you can append `qemu` to your make command
after building for qemu_arm_virt.

### Zig

You can also build this example with the Zig build system:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=<board>
```

The options for `<board>` are the same as the Makefile.

You can simulate QEMU with:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=qemu_arm_virt qemu
```

The final bootable image will be in `zig-out/bin/loader.img`.

## Description
The serial server example system contains two clients which are both able to transmit and receive
characters over serial. The clients are based on the same executable generated from
`examples/serial/serial_server.c`.

The serial server client demonstrates two methods of outputting to serial: the first uses
`sddf_printf` (linked with `_sddf_putchar` defined in `util/putchar_serial.c`), and the second uses
`sddf_putchar_unbuffered` defined in the same file.

The first method demonstrates character buffering based on a flush character or queue capacity, the
second demonstrates characters being transmitted in an unbuffered fashion, typically used by a REPL.

The serial server client sits in an event loop, awaiting notification from the receive virtualiser.
When a notification is received, the client outputs the character in an unbuffered fashion. Every 10
characters the client prints a message in a buffered fashion.

This notification handling process with the receive virtualiser demonstrates how the
*producer_signalled* flag is to be used to prevent against missed notifications from the virtualiser
which could result in missed characters or deadlock.

In this example, **SERIAL_WITH_COLOUR** is enabled so each client prints with a
different colour.

## Documentation
Further documentation for the serial subsystem can be found in `docs/serial.md`