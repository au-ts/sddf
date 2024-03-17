# Serial example

This is an example to show multiple clients being used with a UART driver.

## Building

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board>
```

Currently the options for `MICROKIT_BOARD` are:
* odroidc4
* qemu_arm_virt

After building, the system image to load will be `build/loader.img`.

If you wish to simulate on the QEMU ARM virt platform, you can run the following command:
```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=qemu_arm_virt qemu
```

## Running/using

Upon booting the system image, you will see the following output:

```
Attempting to use the server printf! -- FROM SERVER 2
Enter char to test getchar FOR SERIAL 2
Attempting to use the server printf! -- FROM SERVER 1
Enter char to test getchar FOR SERIAL 1
```
This shows our two clients, `serial_server_1` and `serial_server_2` transmitting to the 
same serial driver through a multiplexer (`virt_rx.c` for receive and `virt_tx.c` for transmit). Both clients will now be waiting on input from the user. 

If we then input the characters 'h' and 'e' to the console, we will get the following output:

```
We got the following char in SERIAL 1: h
Enter char to test getchar -- SERIAL 1
We got the following char in SERIAL 1: e
Enter char to test scanf IN SERIAL 1
```
SERIAL 1 will now be waiting on characters, until the user presses enter. 

To switch input direction to a different client, we can use the following syntax:
```
@<CLIENT CH>
```
In our case, in order to switch to SERIAL 2 we input:

``` 
@2
```

If we now enter the characters 'h' and 'e' to our console, we will get the following:

```
We got the following char in SERIAL 2: h
Enter char to test getchar -- SERIAL 2
We got the following char in SERIAL 2: e
Enter char to test scanf IN SERIAL 2
```
If we continue to add input, and press enter, we get the following:

```
hello there serial 2
---END OF SERIAL 2 TEST---
```
And finally, we can switch back to serial 1:

```
hello there serial 1
---END OF SERIAL 1 TEST---
```


# Implementation Notes

* The virtualiser is currently limited to 9 clients. This is due to only reading the next character after '@' for simplicity. This can be adapted in the future.

* The driver uses the Transmit/Receive FIFO buffers. We interrupt on each character inputted.

* Additionally, manually setting the baud rate is not supported.

* Example implementations using the client for printing/getchar is presented in the serial_server.

* Line Mode or Raw mode can be specified in the driver in the serial configure function call. Basic line mode supports buffering, and deleting for line editing. Raw mode gives characters as they are inputted straight to the virt.

* Echo mode can also be specified in the serial configure function call.
