# Odroid-C4 serial example

This is an example to show multiple clients being used with the Odroid-C4 UART driver.

The register map can be found in sDDF/serial/drivers/hardkernel/include/serial.h.

The relevant documentation can be found online at: https://dn.odroid.com/S905X3/ODROID-C4/Docs/S905X3_Public_Datasheet_Hardkernel.pdf.

## Building

```     
$ make BUILD_DIR=<path/to/build> \
SEL4CP_SDK=<path/to/core/platform/sdk> \
SEL4CP_CONFIG=(benchmark/release/debug)
```

## Running/using

Load the loader.img outputted in the build directory onto an Odroid-C4.

The following is the example output:

```
Attempting to use the server printf! -- FROM SERVER 2
Enter char to test getchar FOR SERIAL 2
Attempting to use the server printf! -- FROM SERVER 1
Enter char to test getchar FOR SERIAL 1

We got the following char in SERIAL 1: h
Enter char to test getchar -- SERIAL 1
We got the following char in SERIAL 1: e
Enter char to test scanf IN SERIAL 1
We got the following char in SERIAL 2: h
Enter char to test getchar -- SERIAL 2
We got the following char in SERIAL 2: e
Enter char to test scanf IN SERIAL 2
hello there serial 2
---END OF SERIAL 2 TEST---
hello there serial 1
---END OF SERIAL 1 TEST---
```

To switch direction of the mux, the following syntax is used:
```
@<CLIENT CH>
```
and the direction will immediately be switched. 

# Implementation Notes

* The mux is currently limited to 9 clients. This is due to only reading the next character after '@' for simplicity. This can be adapted in the future.

* The driver uses the Transmit/Receive FIFO buffers. We interrupt on each character inputted.

* Additionally, manually setting the baud rate is not supported.

* Example implementations using the client for printing/getchar is presented in the serial_server.