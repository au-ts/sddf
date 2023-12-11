#include <microkit.h>
#include <libco.h>
#include "helpers.h"

#include "i2c.h"
#include "printf.h"
#include "i2c-transport.h"

#define DRIVER_CH 0

#define LOG_CLIENT(...) do{ printf("CLIENT|INFO: "); printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ printf("CLIENT|ERROR: "); printf(__VA_ARGS__); }while(0)

// @ivanv: do not like this at all, problem is i2c-transport.c
// already defines these variables
extern uintptr_t req_free;
extern uintptr_t req_used;
extern uintptr_t ret_free;
extern uintptr_t ret_used;

extern ring_handle_t req_ring;
extern ring_handle_t ret_ring;

// size_t read_index = 0;
// uint8_t read_buffer(uint8_t *buffer) {
//     uint8_t value = buffer[RET_BUF_DATA_OFFSET + read_index];
//     read_index += 1;

//     return value;
// }

// #define RESPONSE_DATA_LENGTH (6)
// uint8_t RESPONSE_DATA[RESPONSE_DATA_LENGTH];

// void print_buf(ring_handle_t *ring) {
//      uintptr_t ret_buffer = 0;
//     unsigned int ret_buffer_len = 0;
//     int err = dequeue_used(ring, &ret_buffer, &ret_buffer_len);
//     if (err) {
//         LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
//         return;
//     }

//     uint8_t *buffer = (uint8_t *) ret_buffer;
//     for (int i = 0; i < ret_buffer_len; i++) {
//         LOG_CLIENT("print_buf: buffer[%d] = 0x%lx\n", i, buffer[i]);
//     }
// }

// void read_firwmare_version() {
//     uintptr_t ret_buffer = 0;
//     unsigned int ret_buffer_len = 0;
//     int err = dequeue_used(&ret_ring, &ret_buffer, &ret_buffer_len);
//     if (err) {
//         LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
//         return;
//     }
//     err = dequeue_used(&ret_ring, &ret_buffer, &ret_buffer_len);
//     if (err) {
//         LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
//         return;
//     }
//     uintptr_t ret2_buffer = 0;
//     unsigned int ret2_buffer_len = 0;
//     err = dequeue_used(&ret_ring, &ret2_buffer, &ret2_buffer_len);
//     if (err) {
//         LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
//         return;
//     }
//     uint8_t *buffer = (uint8_t *) ret_buffer;
//     uint8_t *buffer2 = (uint8_t *) ret2_buffer;

//     LOG_CLIENT("return used ring size 0x%lx\n", ring_size(ret_ring.used_ring));
//     LOG_CLIENT("firmware version buffer addr is 0x%lx\n", buffer);

//     // for (int i = 0; i < 8; i++) {
//     //     LOG_CLIENT("buffer[%d] = 0x%lx\n", i, buffer[i]);
//     // }

//     // print_buf(&ret_ring);

//     read_index = 0;
//     if (!(read_buffer(buffer) & 1)) {
//         LOG_CLIENT("buffer[4] is 0x%lx\n", buffer[4]);
//         LOG_CLIENT("read_firmware_version failed!\n");
//         return;
//     }

//     // Read PREAMBLE
//     if (read_buffer(buffer) != PN532_PREAMBLE) {
//         LOG_CLIENT_ERR("read_firmware_version: PREAMBLE check failed\n");
//         return;
//     }
//     // Read STARTCODE1
//     if (read_buffer(buffer) != PN532_STARTCODE1) {
//         LOG_CLIENT_ERR("read_firmware_version: STARTCODE1 check failed\n");
//         return;
//     }
//     // Read STARTCODE2
//     if (read_buffer(buffer) != PN532_STARTCODE2) {
//         LOG_CLIENT_ERR("read_firmware_version: STARTCODE2 check failed\n");
//         return;
//     }
//     // Read length
//     size_t data_length = read_buffer(buffer);
//     // Read checksum of length
//     read_buffer(buffer);
//     // Read response command
//     if (read_buffer(buffer) != PN532_PN532TOHOST) {
//         LOG_CLIENT_ERR("reading response command failed, expected PN532_PN532TOHOST!\n");
//         return;
//     }
//     read_index = 0;
//     if (read_buffer(buffer2) != PN532_CMD_GETFIRMWAREVERSION + 1) {
//         LOG_CLIENT_ERR("reading command number from response failed!\n");
//         return;
//     }
//     // Read command data
//     if (data_length != RESPONSE_DATA_LENGTH) {
//         LOG_CLIENT_ERR("Expected data length to be 6\n");
//         return;
//     }
//     LOG_CLIENT("reading RESPONSE_DATA from buffer addr 0x%lx\n", buffer2);
//     for (int i = 0; i < data_length; i++) {
//         RESPONSE_DATA[i] = read_buffer(buffer2);
//         LOG_CLIENT("RESPONSE_DATA[%d] is 0x%lx\n", i, RESPONSE_DATA[i]);
//     }
//     // Read checksum of data
//     read_buffer(buffer2);
//     // Read postamble
//     read_buffer(buffer2);

//     // @ivanv: should be enqueuing a free buffer here
// }

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#define PN532_CMD_GETFIRMWAREVERSION (0x02)

void client_main(void) {
    LOG_CLIENT("client_main: started\n");
    uint8_t header[1];
    header[0] = PN532_CMD_GETFIRMWAREVERSION;
    write_command(header, 1, NULL, 0);

    uint8_t response_buffer[6];
    read_response(response_buffer, 6);

    LOG_CLIENT("read response!\n");
    for (int i = 0; i < 6; i++) {
        LOG_CLIENT("firmware_version[%d]: 0x%lx\n", i, response_buffer[i]);
    }

    while (1) {}
}

void init(void) {
    LOG_CLIENT("init\n");

    // @ivanv: as we are the client and directly interacting with the driver, we are responsible
    // for initialisting the ring buffer completly (hence why we pass true). we should probably
    // change this to have the driver do the initialisation.
    ring_init(&req_ring, (ring_buffer_t *) req_free, (ring_buffer_t *) req_used, false);
    ring_init(&ret_ring, (ring_buffer_t *) ret_free, (ring_buffer_t *) ret_used, false);
    for (int i = 0; i < I2C_BUF_COUNT; i++) {
        // TODO: check buffer offsetting here. This is definitely too sparse because I haven't updated
        //       it form the 4-buf design
        enqueue_free(&req_ring, (uintptr_t) driver_bufs + (i * I2C_BUF_SIZE), I2C_BUF_SIZE);
        enqueue_free(&ret_ring, (uintptr_t) driver_bufs + (I2C_BUF_SIZE * (i + I2C_BUF_COUNT)), I2C_BUF_SIZE);
    }

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

size_t length = 0;

void notified(microkit_channel ch) {
    switch (ch) {
        case DRIVER_CH:
            LOG_CLIENT("Got notification from driver!\n", ch);
            co_switch(t_main);
            break;
        default:
            LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}
