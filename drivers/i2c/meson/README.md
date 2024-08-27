<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# sddf-i2c-driver

This repo contains an i2c (inter-integrated-circuit) driver for the ODROID C4 Single Board Computer built over the seL4 Device Driver Framework. This repo is structured to be as generic as possible for future extension to other devices.

The initial scope of this driver is to supply an interface to the EE domain i2c controllers on the c4. The ODROID has four interfaces:

* M0: AO or EE domain
* M1: EE domain
* M2: EE domain
* M3: EE domain

All interfaces can operate both in controller (formerly master) and target (formerly slave) mode. We choose to only expose two interfaces as m2 and m3 since the others are not available via external GPIO on the ODROID C4. We chose to only allow the interfaces to operate in master mode as well.

Initially, we effectively ignore the AO domain option for homogeneity (we also will never run this code with EE disabled). This driver is intended to operate the demo system for the [KISS OS](https://github.com/au-ts/kiss) where it will operate the touchscreen and NFC devices.

## Design

* **Each server corresponds to exactly one driver, and the pair represents one logical i2c interface.**
* **Drivers only interface to one explicit i2c bus line interface.**
* **Virtualisers can have many clients.**

Uses custom GPIO and PINMUX configuration.

### Shared Data Region

Clients and Drivers share a mapped data region so the driver and client can communcaite with request and response buffers.
The virtualiser doesnt have access to this data region.

### Shared Request and Response Queues

```
struct i2c_queue_entry {
    /* Offset into the data region for where to look for the request data or
     * where to put the response data */
    size_t offset;
    /* Size of request/response data */
    unsigned int len;
    /* I2C bus address to operate on */
    size_t bus_address;
}
```
Above is the queue structure used for the ring queus.
Each client has a shared response and request queue memory region between each virtualiser they communicate with (N:N relationship).
Each driver has a shared response and request queue memory region to a specific virtualiser (1:1 relationship).

### Clients

Clients must first claim an unclaimed bus address (done using a Protected Procedure Call) in order to communicate with the driver. This is managed by the virtualiser.
Clients build request buffers which the driver has access too and notify the driver by first sending IRQ to virtualiser to authenticate.

### Server (Virtulaiser)

The servers act as the target for API calls from clients and has two responsibilites:

* Demultiplexing: given various client requests, delegate them to the appropriate driver and return results back to the correct caller.
* Security: i2c devices are a colossal security risk if not protected. The driver ensures that the requesting client has been provisioned access to the requested bus and address.
It also maps client specific offsets to driver specific offsets represented in the queue structure.

Each transaction chain can only target a single address - this is adequate for a majority of i2c perpipherals however; very few require multi-address calls in a single transaction. This constraint is to guarantee O(1) rejection of inauthentic requests.

So the server determines if client requests are authentic before enqueuing request into the server <=> driver request queue.
Client requests are put into a queue to guarantee "first-come-first-serve" operation.

The virtualiser maps client specific offsets into driver specific offsets with security checks so clients dont access other clients data.
More details in the virtualiser file.

### Driver

The driver is responsible for hardware interaction. It directly interacts with the i2c hardware via DMA of MMIO registers and is responsible for disassembling the requests from the server into a format which is appropriate for hardware. The token-chain abstraction is very friendly however and as a result translation is minimal. This driver can support many different separate interfaces, each with:

* A unique I2C request list processor / data FIFO.
* A unique interrupt path for data transaction completion from device.
* A unique timer interrupt path from device.

Transactions are broken into the maximum unit acceptable by hardware before yielding.
```
  while (tk_offset < 16 && wdata_offset < 8 && rdata_offset < 8 && request_data_offset < i2c_ifState.curr_request_len) {...};
```

Upon receiving a "processing complete" IRQ the next unit is processed if theres no error.

Once the full transaction has been processed, the server is notified to return data to the client.

Upon each invokation of the driver, all requests in the queue are processed before sleeping to avoid multiplying context switches.

**Important note**: This driver does not implement a polling mode. For extremely long i2c transactions, a polling mode driver (or extending this one to switch) may be preferable. I.e. its potentially more costly to receive lots of IRQs rather then poll.

### Security

Security is currently enforced in a "first-come-first-serve" mode - clients can claim or release an address on a particular bus via a protected procedure call (PPC) to the server. Presently, only one device is allowed access to each address and the server can accept up to 128 claims per interface (allowing one device for every 7-bit address).

### Tokenisation

In transport all i2c operations are decomposed into a list of tokens for more compact handling. i2c has only a few core operations that need expression:

* Write n bytes to an address on the bus,
* Read n bytes to an address on the bus,
* Variations upon the above which do not terminate the transaction.

A token-based abstraction is already used in the ODROID C4 hardware, but we take it a step further by flattening data sent over the bus/request buffers into the token stream too, for easier buffering. The tokens are defined as follows:

* `I2C_TOKEN_END` - Terminator for token lists; has no effect besides to indicate further bytes are invalid (used to represent a certain state of the registers).
* `I2C_TOKEN_START` - Triggers hardware to signal the START condition on the bus, claiming it.
* `I2C_TOKEN_ADDRW` - Transmit a 7 bit address with a WRITE condition.
* `I2C_TOKEN_ADDRR` - Transmit a 7 bit address with a READ condition.
* `I2C_TOKEN_DATA_END` - Transmit a NACK to indicate to the target that we are done reading, if a read was in effect. Required to prevent target from staying in read mode. This is also equivalent to a I2C_TOKEN_DATA token in that is also request a byte of data.
* `I2C_TOKEN_STOP` - Triggers hardware to signal the END condition on the bus, releasing it.
* `I2C_TOKEN_DATA` - Transmits or receives a byte of data - the next byte after this token is treated as the payload to send under a WRITE condition, otherwise under a READ condition the subsequent byte should be another token which is processed normally.

Note: a token is represented as a byte of data.

The format of all request buffers is as follows:
- Begins with a I2C_TOKEN_START.
- Ends with a I2C_TOKEN_STOP.

For a WRITE operation of n bytes within the request:
- Begins with a I2C_TOKEN_ADDRW.
- Followed by n * (I2C_TOKEN_DATA + payload data).

For a READ operation of n bytes within the request:
- Begins with a I2C_TOKEN_ADDRR.
- Followed by (n - 1) * I2C_TOKEN_DATA.
- Concludes with 1 I2C_TOKEN_DATA_END.

A sequence of WRITE and/or READ operations is separated by another I2C_TOKEN_START in a single request, indicating a repeated start condition.

### Error handling and transaction buffer format

The transport layer handles two types of buffers:

* Request buffers: generated by a client to represent a requested transaction.
* Return buffers: generated by the driver to encapsulate returned information from a transaction.

Both these buffers occupy the same space in memory. Ie the return buffer overwrites the request buffer.
There is enough room for this as for READ requests there is a 1:1 ratio almost of amount of request tokens (bytes) to response tokens (bytes).
So what essentially happens is one unit of the request gets overwridden by the respective response received for that transaction.
More details below.

#### Return buffer

The return buffers between the driver and server are used for both data and errors. The first two bytes are returned for an ERROR and TOKEN. All remaining fields are arbitrary tokens or their corresponding payloads for only READs as writes dont return payloads except the error bytes at the start. ERROR is zero for no error, otherwise it is an error code depending on the particular failure. TOKEN contains the index of the token in this transaction that caused the issue. PAY is the payload.

#### Request buffer

The request buffers are used between the clients, server and drivers to represent a complete request. They are passed from the client to the server where they are validated and moved to the driver if authentic. The driver then decomposes the request buffer into some number of hardware operations and placed accordingly in the registers. The format details are already covered above.

#### Example

For READS the request of tokens could be:
```
| 0x0   | 0x1   | 0x2  | 0x3  | 0x4      | 0x5  |
| START | ADDRR | DATA | DATA | DATA_END | STOP |
```
and the repsonse to this will be:

```
| 0x0 | 0x1 | 0x2 | 0x3 | 0x4 |
| ERR | TOK | PAY | PAY | PAY |
```

For WRITES the request of tokens could be:
```
| 0x0   | 0x1   | 0x2  | 0x3 | 0x4  | 0x5 | 0x6  |
| START | ADDRW | DATA | PAY | DATA | PAY | STOP |
```

and the repsonse to this will be:
```
| 0x0 | 0x1 |
| ERR | TOK |
```

Check out the device drivers like PN532 or DS3231 for actual implementations.

## ODROID C4 i2c specifications

For this iteration of this driver:

* 7-bit addressing only
* Access to m2 and m3
* Toggle between standard and fast speeds

The [SOC](https://dn.odroid.com/S905X3/ODROID-C4/Docs/S905X3_Public_Datasheet_Hardkernel.pdf) exposes the i2c hardware via a set of registers. It can operate i2c in software mode (i.e. bit bashing) or using a finite state machine in the hardware which traverses a token list to operate.

### Interface registers
There are a set of registers for each:

**CONTROL**
Contains fields to do bit bashing as well as control flags for the FSM. Can read and write bus levels, contains error and status flags, sets configuration for bus behaviour and controls clocks / list processor.

**SLAVE_ADDR**
Contains the 7-bit target (slave) address as well as some extra fields to control clock stretching and filtering on SDA/SCL.

**TOKEN_LIST 0/1**
Pair of registers each containing a list of 8 4-bit tokens. List 0 contains first token to process at LSB.

**TOKEN_WDATA 0/1**
Pair of registers containing write data for use with the DATA token. Not at all clear how the SoC actually indexes through these - presumably will iterate over them with consequtive data tokens. Each register contains 4 bytes of data corresponding to 4 writes.

**TOKEN_RDATA 0/1**
Pair of registers which are exactly the same as WDATA, but act as a read buffer.

```
struct i2c_regs {
    uint32_t ctl;           // control register
    uint32_t addr;          // slave address and other fields
    uint32_t tk_list0;      // where to put the meson i2c instructions (4 bits long)
    uint32_t tk_list1;      // where to put the meson i2c instructions (4 bits long)
    uint32_t wdata0;        // where to put the write payload from supplied buffer
    uint32_t wdata1;        // where to put the write payload from supplied buffer
    uint32_t rdata0;        // where read data gets put for a response by i2c
    uint32_t rdata1;        // where read data gets put for a response by i2c
};
```

### Transaction token values

Note that the meson token list values (4 bits) are as follows:
```
0x0 | END    | Marks end of token list
0x1 | START  | Captures bus for start of transaction
0x2 | WRADDR | Sends target address with the direction bit set to W
0x3 | RDADDR | Sends target address with direction bit set to R
0x4 | DATA   | Triggers byte read/write depending on direction bit
0x5 | DATAEND| Marks end of a read transfer
0x7 | STOP   | Ends transaction.
```

### m2 registers

**M2_CONTROL**
```
Offset: 0x7400
 paddr: 0xFF822000
```
**M2_SLAVE_ADDR**
```
Offset: 0x7401
 paddr: 0xFF822004
```
**M2_TOKEN_LIST_0**
```
Offset: 0x7402
 paddr: 0xFF822008
```
**M2_TOKEN_LIST_1**
```
Offset: 0x7403
 paddr: 0xFF82200C
```
**M2_TOKEN_WDATA_0**
```
Offset: 0x7404
 paddr: 0xFF822010
```
**M2_TOKEN_WDATA_1**
```
Offset: 0x7405
 paddr: 0xFF822014
```
**M2_TOKEN_RDATA_0**
```
Offset: 0x7406
 paddr: 0xFF822018
```
**M2_TOKEN_RDATA_1**
```
Offset: 0x7407
 paddr: 0xFF82201C
```

### m3 registers

**M3_CONTROL**
```
Offset: 0x7000
 paddr: 0xFF821000
```
**M3_SLAVE_ADDR**
```
Offset: 0x7001
 paddr: 0xFF821004
```
**M3_TOKEN_LIST_0**
```
Offset: 0x7002
 paddr: 0xFF821008
```
**M3_TOKEN_LIST_1**
```
Offset: 0x7003
 paddr: 0xFF82100C
```
**M3_TOKEN_WDATA_0**
```
Offset: 0x7004
 paddr: 0xFF821010
```
**M3_TOKEN_WDATA_1**
```
Offset: 0x7005
 paddr: 0xFF821014
```
**M3_TOKEN_RDATA_0**
```
Offset: 0x7006
 paddr: 0xFF821018
```
**M3_TOKEN_RDATA_1**
```
Offset: 0x7007
 paddr: 0xFF82101C
```
