#include <microkit.h>

#include "i2c.h"
#include "printf.h"
#include "i2c-transport.h"

#define PN532_I2C_BUS_ADDRESS (0x24)
#define PN532_CMD_GETFIRMWAREVERSION (0x02)

#define PN532_PREAMBLE                (0x00)
#define PN532_STARTCODE1              (0x00)
#define PN532_STARTCODE2              (0xFF)
#define PN532_POSTAMBLE               (0x00)

#define PN532_HOSTTOPN532             (0xD4)

size_t data_index = 0;

void enqueue_data(uint8_t *buffer, uint8_t data) {
    buffer[REQ_BUF_DATA_OFFSET + data_index] = data;
    data_index += 1;
}

// @ivanv: do not like this at all, problem is i2c-transport.c
extern uintptr_t req_free;
extern uintptr_t req_used;
extern uintptr_t ret_free;
extern uintptr_t ret_used;

extern ring_handle_t req_ring;
extern ring_handle_t ret_ring;

void init(void) {
    microkit_dbg_puts("I2C client init\n");

    // @ivanv: as we are the client and directly interacting with the driver, we are responsible
    // for initialisting the ring buffer completly (hence why we pass true). we should probably
    // change this to have the driver do the initialisation.
    ring_init(&req_ring, (ring_buffer_t *) req_free, (ring_buffer_t *) req_used, false);
    ring_init(&ret_ring, (ring_buffer_t *) ret_free, (ring_buffer_t *) ret_used, false);

    uint8_t *buffer = NULL;
    uintptr_t buffer_len = 0;
    int ret = dequeue_free(&req_ring, &buffer, &buffer_len);
    if (ret) {
        microkit_dbg_puts("CLIENT|ERROR: could not dequeue free request buffer!\n");
        return;
    }

    // First dequeue shared ringbuffer buffer

    // 1. Talk to the I2C server to claim an address (0x48 >> 1).
    //  1.1 Setup client PD in pos0
    // @ivanv: not sure what the client id should be?
    buffer[REQ_BUF_CLIENT] = 0;
    //  1.2 Setup addr in pos1
    buffer[REQ_BUF_ADDR] = PN532_I2C_BUS_ADDRESS;
    //  1.3 I2C_TK_START
    enqueue_data(buffer, I2C_TK_START);
    enqueue_data(buffer, I2C_TK_ADDRW);

    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, PN532_PREAMBLE);

    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, PN532_STARTCODE1);

    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, PN532_STARTCODE2);
    /* Put length of PN532 data */
    size_t length = 0x1;
    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, length);
    /* Put checksum of length of PN532 data */
    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, ~length + 1);

    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, PN532_HOSTTOPN532);

    /* Actually enqueue GETFIRMWAREVERSION command as the data */
    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, PN532_CMD_GETFIRMWAREVERSION);

    uint8_t sum = PN532_HOSTTOPN532;
    sum += PN532_CMD_GETFIRMWAREVERSION;
    uint8_t checksum = ~sum + 1;
    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, checksum);
    enqueue_data(buffer, I2C_TK_DATA);
    enqueue_data(buffer, PN532_POSTAMBLE);

    enqueue_data(buffer, I2C_TK_END);
}

void notified(microkit_channel ch) {

}
