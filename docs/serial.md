# Introduction to the serial subsystem

The serial subsystem adheres to the sDDF design principles of modularalised components split via
separation of concerns which communicate via shared data structures and microkit channels.

In order to transmit and receive via the uart device, clients of the system must interface with
serial virtualisers, which in turn interface with the uart driver - the only protection domain with
access to the uart device. Characters are passed between components via two shared memory regions -
one a *data region* containing the characters themselves, and the other a *queue region* containing
a queue data structure that allows components to deduce the last position in the data region written
to or read by their neighbour. Queues are implemented as simple ring buffers containing a *head* and
*tail* index, as well as additional *notification flags* which allow components to deduce whether
the consumer of producer of the queue must be notified after a change of queue state has occurred.

The implementation of these data structures, along with helper functions to use them, can be found
in `include/sddf/serial/queue.h`. Further information on how these data structures work, as well as
how components utilise the notification flags to avoid both deadlocks and unnecessary system calls
can be found in the sDDF design document.

## Accessing serial data structures

Clients are advised not to access serial queue and data regions directly, and instead use *serial
queue handles* which contain references to both the queue and data regions, as well as the data
region size. While the queue and data regions are shared between protection domains, queue handles
are not. This allows components to keep size as a local field to prevent tampering, providing
protection against memory faults at invalid offsets due to incorrect changes to size. Utilising the
queue handle also allows clients to make use of the serial queue library, which helps prevent
invalid updates to queue state.

### Transmission

In particular, for transmitting characters, it is recommended to do so via `sddf_printf` (which can
be found in `include/sddf/util/printf.h`), rather than using the serial queue library directly. If
the definition of `sddf_putchar` is linked with `libsddf_util.a` (containing
`util/putchar_serial.c`), rather than `libsddf_util_debug.a` (containing `util/putchar_debug.c`),
`sddf_printf` outputs to the uart device using a simple multiplexing mechanism that vastly reduces
jumbled client output. 

The multiplexing mechanism buffers characters written to the data region by the client, only
notifying the transmit virtualiser when the region becomes full, or the `FLUSH_CHAR` is seen (which
by default is a `\n`).

If your protection domain requires each character to be output to serial individually,
`util/putchar_serial.c` provides a `sddf_putchar_unbuffered` function, which notifies the transmit
virtualiser for each character it receives. Examples of how both `sddf_printf` and
`sddf_putchar_unbuffered` are used can be found in the `serial_server` protection domain in the
serial example. 

Clients may also update serial transmit data structures themselves, using `util/putchar_serial.c` as
a guide. If you wish to use `sddf_printf` linked to serial output, ensure to initialise both the
queue handle and serial putchar library first, details of how to do this can be found below.

### Reception

In contrast to transmission which is client driven, receiving a character is device driven, and data
is passed from the uart driver to the receive virtualiser, and finally to the client. The receive
virtualiser passes non-special characters to whichever client is currently selected to receive
input. By default this is client 0, but can be changed by the user by entering the switch character,
followed by the client number and `SERIAL_TERMINATE_NUM`. Once a character has been written to a
client's data region, the virtualiser will then notify the client depending on the value of the
client's flag.

If a protection domain wishes to receive characters, they must have a dedicated microkit channel to
be notified on by the receive virtualiser, and they must ensure to set their notification flag if
they require a notification upon a character being received. The standard protocol for this is
demonstrated by the serial server protection domain in the serial example.

## Configuration

In `examples/serial/include/serial_config/serial_config.h` you will find a prototype for a serial
config file. This file contains the system configuration information from your `.system` file which
is needed for your serial components and clients to run correctly. It also contains configurable
options for the serial subsystem which are described below:

1. **SERIAL_NUM_CLIENTS** - this defines the number of clients the serial virtualisers will have.

2. **DATA_REGION_SIZES**-  this defines the size of the data regions of each client. While the queue
regions are of fixed size, clients can have variably sized data regions to buffer characters they
wish to receive or transmit. Once data region sizes have been configured in the system and config
file, the client and virtualiser queue initialisation functions should be updated to correctly
initialise their queue handle data structures. Currently, these functions assume that the
virtualiser's shared queue and data regions with their clients are mapped contiguously. This
simplifies the initialisation process, as the virtualiser needs only to know the address of its
first client's queue and data region and may deduce the addresses of the other client's regions from
the size of the queue region and data regions. The subsystem does not require this contiguous layout
to function correctly and any valid layout may be used, as long as the initialisation functions in
the config file are updated accordingly.

3. **SERIAL_TX_ONLY** - enable this if you only want to use the transmit functionality of the serial
subsystem. This stops the uart driver from enabling the receive functionality of the device.

4. **SERIAL_WITH_COLOUR** - enable this if you want client's outputs to be different colours. This
mechanism works by appending a colour code before and after a client's string. Note that the
transmit virtualiser supports up to 256 colours. Also, the transmit virtualiser does not check
client output for colour sequences, so there is no guarantee that clients will only output in their
assigned colour. Upon initialisation, the transmit virtualiser will print the name of each client in
the colour assigned to it.

5. **SERIAL_SWITCH_CHAR** and **SERIAL_TERMINATE_NUM** - these characters control the receive
virtualiser's input switching mechanism. To switch the input stream to a different client, input
**SERIAL_SWITCH_CHAR** followed by up to 4 numeric characters corresponding to the new client
number, and terminate numeric input with **SERIAL_TERMINATE_NUM**. If the system is build in debug
mode, the receive virtualiser will output a success message if the client number you entered is
valid, and error message if invalid. Client 0 receives input by default.

6. **UART_DEFAULT_BAUD** - this determines the baud rate that the uart driver will configure for
the device. Baud rate is always set explicitly instead of detected automatically.

7. **SERIAL_CONSOLE_BEGIN_STRING** - this string is printed by the transmit virtualiser upon
initialisation completion.

If the system file is changed, or the serial subsystem is included into another system, this config
file will need to be edited or re-created to reflect the new system. Be sure to check that the 
`*_init\_sys` functions correctly initialise each protection domains data structures.

## Interfacing with Other Systems
To include the serial subsystem into an existing system, the following steps must be taken:
### **`.system` File** 
You must update your system file to include serial data and queue regions for each client and the
uart driver. You must also include the uart driver, transmit virtualiser, and optionally the receive
virtualiser protection domains. Finally you must include channels between your clients and the
virtualisers, as well as between the virtualisers and the uart driver. The channel numbers that
clients use to notify the virtualisers may be arbitrary, but the virtualisers expect that a
consecutive list of client channels starting from 1. The virtualisers also expect the driver channel
to be 0. The uart driver expects its IRQ channel to be 0, its transmit virtualiser channel to be 1
and its receive virtualiser channel to be 2. Channels may be changed, but they will need to be
updated in the corresponding files.
### **`serial_config` File** 
A new `serial_config` file must be created for your system, containing relevant details of the
system file including client names and data region sizes, as well as updated initialisation
functions for clients and virtualisers.
### **Makefile** 
You must ensure to build the required serial component images (transmit virtualiser and receive
virtualiser). This is most easily done by including the `serial/components/serial_components.mk`
make snippet and ensuring the required components are listed within your images to be built.
Similarly, you must ensure to build the correct uart driver for the device you are building for,
which can most easily be accomplished by including the relevant make snipped (i.e.
`drivers/serial/arm/uart_driver.mk`).

Most serial components and clients will need to include the serial config file, so it is best to put
its directory in your include paths.

For each component you wish to print to serial when using `sddf_printf`, you must ensure they are
linked with `libsddf_util.a` as opposed to `libsddf_util_debug.a` to resolve the definition of
`sddf_putchar`. These libraries can be be built by including `util/util.mk`.

### **Protection Domains**
Each protection domain that prints to serial must include the serial queue library and config file.
They must also have the following declarations - possibly repeated if input is required as well:

```
#define SERIAL_TX_CH 0

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;
```

The channel must match up with the system file, and is used with the queue handle to initialise the
putchar library (by calling`serial_putchar_init`).

Prior to passing the the queue handle to to `serial_putchar_init`, it should first be initialised
with the queue and data region addresses (which will be patched by microkit). A queue handle can be
initialised directly using `serial_queue_init`, however is typically initialised indirectly using
`serial_cli_queue_init_sys` defined in the serial config file. `serial_cli_queue_init_sys`
initialises both the receive and transmit serial queue handles, and allows queue sizes to be
parametrised via the microkit name variable of the client (useful if many clients share the same
executable).

If a client is receiving data, it is recommended to add notification handling code to its notified
function which is invoked in response to a notification from the receive virtualiser. A simple
example of this can be found in the serial example.