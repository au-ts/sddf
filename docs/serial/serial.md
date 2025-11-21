<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
# sDDF Serial Subsystem

## System architecture

The serial subsystem adheres to the sDDF design principles of modular components
split via separation of concerns. Components communicate via shared queues and
data regions, as well as asynchronous notifications (Microkit channels). For a
more in depth discussion of these design principles and how the serial subsystem
incorporates them, see the [sDDF design document](/docs/design_doc).

The UART driver protection domain handles all UART device interrupts, and is the
only protection domain with access to the UART registers. In order to safely
share the UART device, the UART driver interfaces with a pair of serial
virtualisers which in turn multiplex client input and output. The serial
transmit virtualiser is responsible for multiplexing client output, while the
serial receive virtualiser is responsible for deciding which characters are
directed to which client.

### Serial Queues

To pass characters between components two shared memory regions are used - a
*data region* where characters are written to and read from, and a *queue*
region which imposes a ring buffer structure on the data region. The queue keeps
track of the *head* and *tail* indices, the head being the next index of the
data region to be read from, and the tail being the next index of the data
region to be written to. Head and tail indices are kept as overflowing unsigned
integers, and must be used modulo *queue capacity* when accessing queues. This
enforces the constraint that queue capacity must be a power of two.

All sDDF queues are single-producer single-consumer, and as a consequence the
head index must only be written to by the consumer of the queue, and the tail
index must only be written to by the producer of the queue. This allows the
queues to be used without a lock, with the only concurrency concern being the
consistency of the order of queue operations which is achieved with memory
barriers.

The *serial_queue* data structure contains the queue head, tail and
*producer_signalled* notification flag [described below](#signalling), while
*serial_queue_handle* data structure contains a pointer to the serial queue, the
queue capacity and a pointer to the data region. The serial queue and data
regions reside in separate shared memory regions, while the queue handle resides
in local memory ensuring that queue capacity may not be modified by untrusted
clients which could result in out of bound data region accesses. Serial queue
library functions are written to take serial queue handles as arguments, so it
is recommended to use serial queue handles over raw serial queues.

The implementation of the serial queue and serial queue handle along with the
serial queue library functions can be found in the [serial queue
library](/include/sddf/serial/queue.h).

### Serial Communication Protocols {#signalling}

When a producer has enqueued characters in a queue, or a consumer has dequeued
characters from a queue, we say that *work* has been performed on the queue. In
order for further work to be performed, it is typically the case that the
working component will need to signal its neighbour in order for it to be
scheduled.

In the case of work being performed by the producer, the consumer of the queue
will unconditionally be signalled. In contrast, if work is performed by the
consumer of a queue, this is only relevant to the producer of the queue if it is
awaiting free space to enqueue additional characters. To minimise unnecessary
signals from the consumer to the producer, the serial subsystem utilises a
*notification flag* for the producer to indicate to the consumer that it
requires a signal if more space has become available. If upon finishing
dequeueing characters the consumer finds the *producer_signalled* flag set to
false, it will set the flag to true and signal its neighbour.

This procedure of signalling based on the value of a *notification flag* is an
instance of the *sDDF signalling protocol*, and is written in such a way to
prevent deadlocks from race conditions. Further information on the specifics of
this protocol can also be found in the [sDDF design document](/docs/design_doc).
Failure to follow this protocol when interfacing with sDDF components may result
in data processing delays, or in the worst case deadlocks.

## Transmission

For a client to transmit characters, it must first write these characters to the
data region it shares with the transmit virtualiser, then update the tail of the
queue making the addition of these characters visible to the transmit
virtualiser. Finally, it must signal the virtualiser to ensure it is scheduled
to pass the characters to the driver.

Since the serial subsystem typically handles the output of more than one client
at a time, a method has been developed to enable a degree multiplexing output
between clients. To support transmission without interference, clients can
optionally enqueue entire strings at a time in their data regions, only updating
the shared tail of the queue and signalling when either a *flush* character is
scene (by default a '\n'), or when the data region is full. This means that when
the transmit virtualiser copies the data from a client's buffer into the
driver's buffer, it will not be interrupted by the output of other clients,
vastly improving the readability of the system's output.

Unfortunately this method is not foolproof however, as Microkit debug output
will always take precedence over the UART driver possibly interrupting client
strings. Also, this multiplexing method will only work successfully if *all*
clients batch their output in this way.

Depending on how you would like your client's output to be handled, there are
three general methods you can choose from to interface your client with the
transmit virtualiser:

1. Use the serial queue library functions. `serial_enqueue` enqueues a single
   character into a queue and updates the shared tail immediately, making the
   character available to be transmitted out the UART. `serial_enqueue_local`
   writes a character to the data region, but updates a local version of the
   tail rather than the shared tail, allowing a client to batch enqueue
   characters without making them visible. When a batch of characters is ready
   to be transmitted `serial_update_shared_tail` can be used to make the batch
   visible. `serial_enqueue_batch` can also be used to enqueue a buffer of
   characters into the queue, which updates the shared tail upon completion.

   All of these methods still require a signal to the virtualiser afterwards to
   ensure it is scheduled to process the queue.

2. Link the client elf file with the [sDDF utility library](/util/)
   (libsddf_util.a). This gives clients access to `sddf_printf` and
   `sddf_dprintf` (which only outputs in debug configurations) which are linked
   with `sddf_putchar`. `sddf_putchar` calls `serial_enqueue_local` on
   characters of strings outputted using `sddf_[d]printf`, only updating the
   shared tail when the flush character is seen, or the data region is full. The
   transmit virtualiser will also be signalled upon updating the shared tail.

   In order to use this method, the `sddf_putchar` library will need to be
   initialised before calling `sddf_[d]printf` so that the transmit queue handle
   and serial transmit virtualiser Microkit channel are known to the library.

   If a protection domain only needs to be able to print in debug
   configurations, it can instead be linked with `libsddf_util_debug.a`, which
   does not require it to be a client of the serial subsystem, nor does it
   require initialisation. In this case, sddf_[d]printf will be linked with the
   debug version of `sddf_putchar` which will similarly batch output until a
   flush character or character limit is seen before calling
   `microkit_dbg_puts`.

3. Write your own custom interface functions. The client may write to the data
   region itself without using any of the `serial_enqueue*` functions. Care must
   be taken to ensure that the queue is not written past its capacity (which
   would overwrite valid data), and that the tail is updated using the correct
   memory barriers (it is still recommended to use `serial_update_shared_tail`
   to update the tail which will check for overwriting existing data and handle
   memory safety). [LionOS NFS
   component](https://github.com/au-ts/lionsos/blob/main/components/fs/nfs/posix.c)
   shows one example of a custom output function. Similarly [LionsOS Micropython
   component](https://github.com/au-ts/lionsos/blob/main/components/micropython/mphalport.c)
   demonstrates an example of a *lossless* output function, where in the case of
   the transmit data region being full Micropython requests a signal from the
   transmit virtualiser and waits until there is space in the data region before
   continuing transmission.

For each of these methods, special care must be taken to consider the following
cases:

### Carriage Returns

Whether a `\r` should be added automatically to client output preceding a `\n`.
`sddf_putchar` does this automatically when using `sddf_[d]printf`.

### Reaching Data Region Capacity

How to handle the data region hitting capacity. The `serial_enqueue*` functions
will return with an error if called when the queue is full. When the queue
reaches capacity, it is recommended that the serial virtualiser is signalled
immediately to prevent data loss, as is done in `sddf_putchar`. However, if the
client attempts to output more data before the virtualiser is able to clear from
the data region, this data will be lost. In order to gracefully handle this
case, it is best for the client to set the `producer_signalled` flag to false
which will result in the transmit virtualiser signalling the client when there
is free space available in the queue. This will require the client to keep track
of output awaiting space in the transmit data region. A simpler way to avoid
this problem is to set the capacity of a client's data region large enough to
buffer all possible bursts of output.

## Reception

In contrast to transmission which is client driven, receiving a character is
device driven, and the decision as to which client receives which character is
driven by the stream of characters themselves. When a character is received, the
interrupt is handled by the UART driver which copies all available characters to
the receive virtualiser's data region, conditional on the region having
available space. The tail of the shared queue is then updated accordingly, and
the receive virtualiser is signalled.

Characters are categorised by the receive virtualiser as either *special* or
*ordinary*. All ordinary characters are written directly to the data region of
the *current client*, which by default is client 0 but can be re-configured at
run time using special characters. Special characters are not passed to the
current client, and instead are used to change the *state* of the receive
virtualiser allowing the current client to be updated.

The receive virtualiser has three states:
1. *normal* - Any received character that is not the *switch character* will be
   passed directly to the current client. Once the receive virtualiser finishes
   processing all characters in the driver data region, the shared tail will be
   update and the current client will be signalled. If the switch character is
   received, the virtualiser will change state to the *switched* state.

2. *switched* - In the switched state, the virtualiser expects to receive a
   decimal number corresponding to the next desired current client. Entering the
   switch character again *escapes* the character, resulting in the switch
   character being passed to the current client, and the state returning to
   normal. If a digit character is received, it will be interpreted as the first
   digit of the next current client, and will change the virtualiser state to
   *number*. If any other character is entered, it will be treated as erroneous
   input. The character will not be passed to the current client, and the state
   will return to normal with no change in current client.

3. *number* - The number state allows the user to enter up to `MAX_CLI_BASE_10 -
   1` more numbers making up the decimal representation of the next current
   client. No characters entered in this state will ever be transferred to
   clients. If more than the maximum digits are entered, or a non digit
   character is received, this will be treated as erroneous input and will
   return the state to normal with no change to current client. Once the desired
   client number is entered, the *terminate number character* must be entered to
   finalise the next selected current client. If the client number entered
   matches an existing client, the shared tail of the old current client's queue
   will be updated and it will be signalled before the current client is
   changed. Entering an invalid client number will return the virtualiser to the
   normal state without any change to the current client.

The two special characters *switch_char* and *terminate_num_char* are
configurable using the [Microkit sdfgen
tool](https://au-ts.github.io/microkit_sdf_gen/).

If the current client's receive data region is full at the time of a character
being enqueued, the new character will be dropped. This ensures that the receive
virtualiser may continue making progress regardless of the state of a client's
queue.

## Using the Serial Subsystem in your System

If you wish to use a platform that is not yet supported, you will need to create
your own UART driver to interface with the serial receive and transmit
virtualisers. See [here](/docs/developing.md) for tips on how to do this and
[drivers.md](/docs/drivers.md) for an existing list of all serial devices
supported.

### SDF Generator Tool

It is highly recommended to use the [Microkit sdfgen
tool](https://au-ts.github.io/microkit_sdf_gen/) to create sDDF and LionsOS
systems. To add a *serial system* within a Python meta program, it is as simple
as creating the UART driver and serial virtualiser protection domains and
passing them into the serial subsystem:
```py
from sdfgen import SystemDescription, Sddf

ProtectionDomain = SystemDescription.ProtectionDomain

serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=198)
serial_virt_rx = ProtectionDomain("serial_virt_rx", "serial_virt_rx.elf", priority=199)

# Providing a virt rx is optional
serial_system = Sddf.Serial(sdf, serial_node, serial_driver, serial_virt_tx, virt_rx=serial_virt_rx)
```

Where the serial node is obtained from the board's device tree, and sdf is the
system description instance. Note that priorities of serial components and
clients are all *configurable*, however the system is designed with the
assumption that the driver runs at the highest priority, followed by the
virtualisers and finally the clients. For further documentation on the options
which can be provided when creating a serial subsystem, or using the Microkit
sdfgen tool in general, you can check the documentation
[here](https://au-ts.github.io/microkit_sdf_gen/).

Adding a protection domain as a client of the system is as simple as:
```py
client = ProtectionDomain("client", "client.elf", priority=1)
serial_system.add_client(client)
```

Additionally, clients of the serial subsystem will require the relevant serial
data structures described in the [Interfacing with
Clients](#interfacing-with-clients) section below.

Currently the serial subsystem supports either *transmit only* mode, or *receive
and transmit* where all clients are configured to be able to receive characters.
If the serial subsystem is created *without* a receive virtualiser, then it will
be transmit only. If a receive virtualiser is provided, then each client will be
given the ability to receive characters. In the future, receive and transmit
ability will be decided on a per client basis as each client is added to the
system.

### Interfacing with Clients

The Microkit sdfgen tool will create all the serial resources required for each
serial component. The virtual addresses of memory regions and channel values
will be placed into serialised C structs and written to `.data` files in the
build directory for each serial component. These structs are called *config*
structures, and the *serial* config structures are defined
[here](/include/sddf/serial/config.h). Once the meta program has completed, the
makefile will use a series of `OBJCOPY`s to update the corresponding sections in
each elf file. This gives components access to these values at boot time.

The `OBJCOPY` commands are in the makefile snippets, and look as follows:
```sh
$(OBJCOPY) --update-section .serial_client_config=serial_client_client0.data client0.elf
```
When a new serial client is added to the system, an additional `OBJCOPY` command
must be added to the makefile snippet to ensure the client's elf is updated
accordingly.

Each serial client must declare a `serial_client_config_t` struct to be updated
with values obtained from the meta program. Clients must also declare serial
queues which will be initialised with values from the config struct. Typically,
a client's serial declarations will look as follows:
```c
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;
```

These queues will need to initialised in the `init` function as follows:
```c
serial_queue_init(&rx_queue_handle, serial_config.rx.queue.vaddr, serial_config.rx.data.size, serial_config.rx.data.vaddr);
serial_queue_init(&tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size, serial_config.tx.data.vaddr);
```

Additionally, if a client wishes to use `sddf_[d]printf`, this library will also
need to be included and initialised after the queues have been initialised:
```c
#include <sddf/util/printf.h>

serial_putchar_init(serial_config.tx.id, &tx_queue_handle);
```

As described in the [Transmission](#transmission) section, clients can either
output using `sddf_[d]printf`, or by writing characters to the queues directly
using `serial_enqueue[_local]` followed by `microkit_signal` to the serial
transmit virtualiser channel (`serial_config.tx.id`).

When a client receives characters, it will be signalled by the receive
virtualiser on channel `serial_config.rx.id`. Receiving characters is typically
done in a loop using `serial_dequeue`:
```c
char c;
while (!serial_dequeue(&rx_queue_handle, &c)) {
   ...
}
```

Note that if a client's data region is full at the time when the receive
virtualiser tries to enqueue a character, the character will be dropped.

### Building Components and Libraries

Our build system relies on makefile snippets to build sDDF components and
libraries. The serial components that are required to use the subsystem are:
* The corresponding UART driver for your platform. The C code and makefile
  snippet for the driver can be found in the platform directory
  [here](/drivers/serial/).
* The serial virtualisers. The receive virtualiser is optional depending on
  whether your system requires receive access. The C code and makefile snippet
  can be found [here](/serial/components/serial_components.mk).

You will need to include these snippets in your makefile to build the UART
driver and serial virtualisers.

Both the UART driver and serial virtualisers rely on the sDDF debug utility
library (`libsddf_util_debug.a`, which uses `microkit_dbg_puts`) for debug
prints and assertions. The serial version of `sddf_[d]printf` is also defined in
the non-debug version of this library (`libsddf_util.a`). The
[snippet](/util/util.mk) which builds both these libraries will need to be
included in your makefile.

Serial components assume that `libsddf_util_debug.a` is present in `${LIBS}`. If
a client wishes to print via the serial subsystem, `libsddf_util.a` must be
listed prior to `libsddf_util_debug.a`.

#### Include Paths

Serial components and clients will need to have the top level [sDDF
include](/include/) in their `CFLAGS` to access sDDF library functions as well
as serial configuration structs.

## Running and Using

An example system utilising both the transmit and receive functionality of the
serial subsystem can be found [here](/examples/serial/). The
[README](/examples/serial/README.md) describes how to build and run the system
as well as expected output.
