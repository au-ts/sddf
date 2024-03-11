<!--
   Copyright 2022, UNSW
   SPDX-License-Identifier: CC-BY-SA-4.0
-->

libsharedringbuffer
-------------------

This directory contains a library implementation of shared ring
buffers for the transportation of data. This is intended to be used as a
communication mechanism between system components for bulk data transfer,
and was originally created as a data plane between an ethernet driver and
network stack for the sDDF. This library doesn't contain any code that
interfaces with seL4. It is expected that the user will provide shared
memory regions and notification/signalling handlers to this library.

To use this library in a project you can link `shared_ringbuffer` in your
target applications CMake configuration.

This libary is intended to be used by both a producer and a consumer. For
example, an ethernet driver produces data for a network stack to consume.
Two separate shared memory regions are required for each ring handle; one
to store free buffers and one to store used buffers. Each ring buffer
contains a separate head index to insert at and tail index to remove from. 
The producer only writes to the head index, and the consumer only writes 
to the tail index. As read and writes of a small integers are atomic, we 
can gaurantee the consistency of the ring buffers without the use of 
locks.
The size of the ring buffers defaults to NUM_BUFFERS 512. The user must
ensure that the shared memory regions handed to the library are of
appropriate size to match this.

Use case
---------

This library is intended to be used with a separate shared memory region,
usually allocated for DMA for a driver. The ring buffers can then contain
offsets into these shared memory regions, indicating which buffers are in 
use or available (free) to be used by either component.
Typically, 2 shared ring buffers are required, with separate structures
required on the recieve path and transmit path. Thus there are 4 regions
of shared memory required: 1 storing offsets of free RX buffers, 1 storing 
offset to used RX buffers, 1 storing offsets to TX buffers, and another 
storing offsets to free TX buffers.

On initialisation, both the producer and consumer should allocate their
own ring handles (`struct ring_handle`). These data structures simply
store pointers to the actual shared memory regions and are used to
interface with this library. The ring handle should then be passed into
`ring_init` along with 2 shared memory regions and the number of places 
the ring buffer can use to store buffers (size of the ring buffer).

After initialisation, a typical use case would look like:
The driver wants to add a buffer that will be read by another component
(for example, a network stack processing incoming packets).

    1. The driver dequeues a buffer from the free ring containing an 
    offset into the corresponding shared memory region. This will point
    to a buffer which can safely be written to.
    2. Once data is inserted into the buffer (eg. via DMA), the driver
    then enqueues the buffer into the used ring.
    3. The driver can then check with the receiver requires a notification
    when a buffer is added to the used ring by checking the consumer 
    notified flag. If this flag is false, the driver will signal the 
    consumer.
    4. Similarly, the reciever receives the signal or continues its ring
    processing and finds that a packet has been enqueued in the used ring.
    It then processes the data, and once finished, enqueues the buffer 
    back into the free ring to be used once more by the driver.

Head/Tail Mechanism
-------------------

Buffers from head through to tail - 1 inclusive are available to be used. Producers
insert at the tail index and consumers remove from the head index.

T = Tail
H = Head
E = Empty
F = Full

If non-empty, the ring looks like either:
0 <= T <= H < LENGTH
[ E | E | HF | F | F | F | F | TE | E | E ]

               OR

0 <= H < T < LENGTH
[ F | F | F | TE | E | E | E | HF | F | F ]