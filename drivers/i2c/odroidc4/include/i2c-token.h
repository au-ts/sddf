/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c-token.h
// This file specifies the tokens used in the transport layer
// between the i2c server and driver. This is a lower level abstraction
// which is more closely aligned to how the hardware handles transactions.
//
// This file also specifies the structure of a token buffer between server/driver.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

// This paradigm is based on the S905X3's I2C interface - it is a nice level of abstraction
// however that should be very pleasant to translate to other interfaces. I extend this by
// removing the need for separate read, write and token buffers allowing data to be stored in
// 1D buffers indexed by libsharedringbuffer

#ifndef I2C_TK_H
#define I2C_TK_H

#include <stdint.h>
typedef uint8_t i2c_token_t;

#define I2C_TK_END      0x0     // END: Terminator for token list, has no meaning to hardware otherwise
#define I2C_TK_START    0x1     // START: Begin an i2c transfer. Causes master device to capture bus.
#define I2C_TK_ADDRW    0x2     // ADDRESS WRITE: Used to wake up the target device on the bus. Sets up
                                //                any following DATA tokens to be writes.
#define I2C_TK_ADDRR    0x3     // ADDRESS READ: Same as ADDRW but sets up DATA tokens as reads.
// 0x4 is skipped in case these #defines are accidentally used instead of the odroid ones
#define I2C_TK_DATA_END 0x5     // DATA_LAST: Used for read transactions to write a NACK to alert the slave device
                                //            that the read is now over.
#define I2C_TK_STOP     0x6     // STOP: Used to send the STOP condition on the bus to end a transaction. 
                                //       Causes master to release the bus.

#define I2C_TK_DAT      0x7     // Read or write one byte - the byte after this is treated as payload.

#endif