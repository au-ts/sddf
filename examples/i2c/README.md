# I<sup>2</sup>C example

This example makes use of the DS3231 RTC and NXP PN532 card-reader.
Documentation and more specific infomation about each can be found below.

This example is intended to run on an Odroid-C4 using the I2C connected via GPIO pins 3 and 5
for SDA and SCL respectively.

## Before compiling

Change the virt.c file to fulfil your examples needs: i.e. 1 or 2 clients, channel numbers etc...
Or comment out the client you dont want to use.

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

## Running PN532
Make sure PN_532_ON is defined.

Running the example will show the following output after the system has booted:
```
CLIENT|ERROR: Timed out waiting for a card
CLIENT|ERROR: Timed out waiting for a card
```

If you put a card in front of the card reader, you should see messages similar to
the following:
```
UID Length: 4 bytes
UID Value:  0x9c 0x1b 0xb4 0x1
UID Length: 4 bytes
UID Value:  0x9c 0x1b 0xb4 0x1
UID Length: 4 bytes
UID Value:  0x9c 0x1b 0xb4 0x1
```

Where the card UID is being read and printed out.

Note that for MiFare Ultra Light cards or cards that have encryption, you may
see timeouts between each UID card read, this is expected.

**There is a video in this directory of the card reader working.**

## Running DS3231
Make sure DS_3231_ON is defined.

Running the example will show the following output after the system has booted:
```
Set Date and Time on DS3231 to: 31-12-23 23:59:40 (Sunday)
Date and Time: 31-12-23 23:59:40 (Sunday)
Date and Time: 31-12-23 23:59:40 (Sunday)
Date and Time: 31-12-23 23:59:41 (Sunday)
Date and Time: 31-12-23 23:59:41 (Sunday)
Date and Time: 31-12-23 23:59:42 (Sunday)
Date and Time: 31-12-23 23:59:42 (Sunday)
```

## Running DS3231+PN532
Running the example will show simliar to the following output after the system has booted:
Basically its a mix between output from the pn532 and the ds3231 output:

```
Set Date and Time on DS3231 to: 31-12-23 23:59:42 (Sunday)
Date and Time: 31-12-23 23:59:42 (Sunday)
Date and Time: 31-12-23 23:59:42 (Sunday)
CLIENT|ERROR: Timed out waiting for a card
Date and Time: 31-12-23 23:59:43 (Sunday)
Date and Time: 31-12-23 23:59:43 (Sunday)
CLIENT|ERROR: Timed out waiting for a card
Date and Time: 31-12-23 23:59:44 (Sunday)
Date and Time: 31-12-23 23:59:44 (Sunday)
UID Length: 7 bytes
UID Value:  0x4 0x4d 0x27 0x8a 0x25 0x10 0x90
Date and Time: 31-12-23 23:59:45 (Sunday)
Date and Time: 31-12-23 23:59:45 (Sunday)
CLIENT|ERROR: Timed out waiting for a card
Date and Time: 31-12-23 23:59:46 (Sunday)
Date and Time: 31-12-23 23:59:46 (Sunday)
UID Length: 7 bytes
UID Value:  0x4 0x4d 0x27 0x8a 0x25 0x10 0x90
Date and Time: 31-12-23 23:59:47 (Sunday)
Date and Time: 31-12-23 23:59:47 (Sunday)
CLIENT|ERROR: Timed out waiting for a card
```