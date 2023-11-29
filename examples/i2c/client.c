#include <microkit.h>

#include "i2c.h"
#include "printf.h"
#include "i2c-transport.h"

#define DRIVER_CH 0

#define LOG_CLIENT(...) do{ printf("CLIENT|INFO: "); printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ printf("CLIENT|ERROR: "); printf(__VA_ARGS__); }while(0)

#define PN532_I2C_BUS_ADDRESS (0x48 >> 1)
#define PN532_CMD_GETFIRMWAREVERSION (0x02)

#define PN532_PREAMBLE                (0x00)
#define PN532_STARTCODE1              (0x00)
#define PN532_STARTCODE2              (0xFF)
#define PN532_POSTAMBLE               (0x00)

#define PN532_HOSTTOPN532             (0xD4)

size_t data_index = 0;

enum client_state {
    INIT,
    READ_ACK_FRAME,
    CHECK_ACK_FRAME_RESPONSE,
    READ_FIRMWARE_VERSION,
    READ_RESPONSE_LENGTH,
    READ_RESPONSE,
    REQUEST_READ_RESPONSE,
};

enum client_state state;

void enqueue_data(uint8_t *buffer, uint8_t data) {
    buffer[REQ_BUF_DATA_OFFSET + data_index] = data;
    data_index += 1;
}

// @ivanv: do not like this at all, problem is i2c-transport.c
// already defines these variables
extern uintptr_t req_free;
extern uintptr_t req_used;
extern uintptr_t ret_free;
extern uintptr_t ret_used;

extern ring_handle_t req_ring;
extern ring_handle_t ret_ring;

// 1. Do get firmware version command
// 2. Process the response to that
// 3. Read ack frame
// 4. Process response to ack frame
// 5. Check if response first byte is 0
// 6. if data[0] == 0 goto 3

size_t read_index = 0;
uint8_t read_buffer(uint8_t *buffer) {
    uint8_t value = buffer[RET_BUF_DATA_OFFSET + read_index];
    read_index += 1;

    return value;
}

uint8_t RESPONSE_DATA[4];

void read_firwmare_version() {
    uintptr_t ret_buffer = 0;
    unsigned int ret_buffer_len = 0;
    int err = dequeue_used(&ret_ring, &ret_buffer, &ret_buffer_len);
    if (err) {
        LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
        return;
    }
    uint8_t *buffer = (uint8_t *) ret_buffer;

    LOG_CLIENT("return used ring size 0x%lx\n", ring_size(ret_ring.used_ring));

    for (int i = 0; i < 8; i++) {
        LOG_CLIENT("buffer[%d] = 0x%lx\n", i, buffer[i]);
    }

    read_index = 0;
    if (!(read_buffer(buffer) & 1)) {
        LOG_CLIENT("buffer[4] is 0x%lx\n", buffer[4]);
        LOG_CLIENT("read_firmware_version failed!\n");
        return;
    }

    // Read PREAMBLE
    read_buffer(buffer);
    // Read STARTCODE1
    read_buffer(buffer);
    // Read STARTCODE2
    read_buffer(buffer);
    // Read length
    size_t data_length = read_buffer(buffer);
    // Read checksum of length
    read_buffer(buffer);
    // Read response command
    read_buffer(buffer);
    read_buffer(buffer);
    // Read command data
    if (data_length > 4) {
        LOG_CLIENT_ERR("Expected data length to be 4\n");
        return;
    }
    for (int i = 0; i < data_length; i++) {
        RESPONSE_DATA[i] = read_buffer(buffer);
        LOG_CLIENT("RESPONSE_DATA[%d] is 0x%lx\n", i, RESPONSE_DATA[i]);
    }
    // Read checksum of data
    read_buffer(buffer);
    // Read postamble
    read_buffer(buffer);

    // @ivanv: should be enqueuing a free buffer here
}

void request_read_response(size_t length) {
    uintptr_t req_buffer = 0;
    unsigned int buffer_len = 0;
    int ret = dequeue_free(&req_ring, &req_buffer, &buffer_len);
    if (ret) {
        LOG_CLIENT_ERR("could not dequeue free request buffer!\n");
        return;
    }

    uint8_t *buffer = (uint8_t *) req_buffer;

    data_index = 0;
    buffer[REQ_BUF_CLIENT] = 0;
    buffer[REQ_BUF_ADDR] = PN532_I2C_BUS_ADDRESS;

    // @ivanv: hack since we're not reading the right length yet
    length = 4;
    LOG_CLIENT("===== length is 0x%lx\n", length);
    enqueue_data(buffer, I2C_TK_START);
    enqueue_data(buffer, I2C_TK_ADDRR);
    for (int i = 0; i < 6 + length + 2; i++) {
        enqueue_data(buffer, I2C_TK_DATA);
    }
    enqueue_data(buffer, I2C_TK_STOP);
    enqueue_data(buffer, I2C_TK_END);

    ret = enqueue_used(&req_ring, req_buffer, data_index + 2);
    if (ret) {
        LOG_CLIENT_ERR("failed to enqueue request buffer!\n");
    }

    LOG_CLIENT("sent request_read_response request\n");
    microkit_notify(DRIVER_CH);
}

void nack() {
    const uint8_t PN532_NACK[] = {0, 0, 0xFF, 0xFF, 0, 0};

    uintptr_t req_buffer = 0;
    unsigned int buffer_len = 0;
    int ret = dequeue_free(&req_ring, &req_buffer, &buffer_len);
    if (ret) {
        LOG_CLIENT_ERR("could not dequeue free request buffer!\n");
        return;
    }

    uint8_t *buffer = (uint8_t *) req_buffer;

    data_index = 0;
    buffer[REQ_BUF_CLIENT] = 0;
    buffer[REQ_BUF_ADDR] = PN532_I2C_BUS_ADDRESS;
    enqueue_data(buffer, I2C_TK_START);
    enqueue_data(buffer, I2C_TK_ADDRW);
    for (int i = 0; i < sizeof(PN532_NACK); i++) {
        enqueue_data(buffer, I2C_TK_DATA);
        enqueue_data(buffer, PN532_NACK[i]);
    }
    enqueue_data(buffer, I2C_TK_STOP);
    enqueue_data(buffer, I2C_TK_END);

    ret = enqueue_used(&req_ring, req_buffer, data_index + 2);
    if (ret) {
        LOG_CLIENT_ERR("failed to enqueue request buffer!\n");
    }

    LOG_CLIENT("sent nack request\n");
    microkit_notify(DRIVER_CH);
}

size_t read_response_length() {
    uintptr_t ret_buffer = 0;
    unsigned int ret_buffer_len = 0;
    int err = dequeue_used(&ret_ring, &ret_buffer, &ret_buffer_len);
    if (err) {
        LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
        return 0;
    }
    uint8_t *buffer = (uint8_t *) ret_buffer;
    data_index = 0;

    if (buffer[RET_BUF_DATA_OFFSET] & 1) {
        return buffer[RET_BUF_DATA_OFFSET + 4];
    } else {
        LOG_CLIENT("read_response_length failed!\n");
        return 0;
    }

    // @ivanv: should be enqueuing a free buffer here
}

void get_response_length() {
    // LOG_CLIENT("Ready to read firmware version!\n");

    uintptr_t req_buffer = 0;
    unsigned int buffer_len = 0;
    int ret = dequeue_free(&req_ring, &req_buffer, &buffer_len);
    if (ret) {
        LOG_CLIENT_ERR("could not dequeue free request buffer!\n");
        return;
    }

    uint8_t *buffer = (uint8_t *) req_buffer;

    data_index = 0;
    buffer[REQ_BUF_CLIENT] = 0;
    buffer[REQ_BUF_ADDR] = PN532_I2C_BUS_ADDRESS;
    enqueue_data(buffer, I2C_TK_START);
    enqueue_data(buffer, I2C_TK_ADDRR);
    for (int i = 0; i < 6; i++) {
        enqueue_data(buffer, I2C_TK_DATA);
    }
    enqueue_data(buffer, I2C_TK_STOP);
    enqueue_data(buffer, I2C_TK_END);

    ret = enqueue_used(&req_ring, req_buffer, data_index + 2);
    if (ret) {
        LOG_CLIENT_ERR("failed to enqueue request buffer!\n");
    }

    LOG_CLIENT("sent get_response_length request\n");
    microkit_notify(DRIVER_CH);
}

uint8_t check_ack_frame_response() {
    /* Assumes that read_ack_frame has been called and we have something ready in
       the return buffer to read. */
    const uint8_t PN532_ACK[] = {0, 0, 0xFF, 0, 0xFF, 0};

    LOG_CLIENT("return used ring size: 0x%lx\n", ring_size(ret_ring.used_ring));

    uintptr_t ret_buffer = 0;
    unsigned int ret_buffer_len = 0;
    int err = dequeue_used(&ret_ring, &ret_buffer, &ret_buffer_len);
    if (err) {
        LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
        return 0;
    }

    LOG_CLIENT("return buffer 0x%lx with size 0x%lx\n", ret_buffer, ret_buffer_len);

    uint8_t *buffer = (uint8_t *) ret_buffer;

    LOG_CLIENT("RET_BUF_ERR is 0x%lx\n", buffer[RET_BUF_ERR]);
    if (buffer[RET_BUF_DATA_OFFSET] & 1) {
        for (int i = 0; i < 6; i++) {
            if (buffer[RET_BUF_DATA_OFFSET + 1 + i] != PN532_ACK[i]) {
                LOG_CLIENT_ERR("Ack malformed!\n");
            }
        }
        return true;
    } else {
        LOG_CLIENT("device not ready yet!\n");
    }

    return false;
}

void read_ack_frame() {
    LOG_CLIENT("reading ack frame!\n");

    uintptr_t req_buffer = 0;
    unsigned int buffer_len = 0;
    int ret = dequeue_free(&req_ring, &req_buffer, &buffer_len);
    if (ret) {
        LOG_CLIENT_ERR("could not dequeue free request buffer!\n");
        return;
    }

    uint8_t *buffer = (uint8_t *) req_buffer;

    /* Reset global data index, this is kind of bad/fragile */
    data_index = 0;

    buffer[REQ_BUF_CLIENT] = 0;
    buffer[REQ_BUF_ADDR] = PN532_I2C_BUS_ADDRESS;
    enqueue_data(buffer, I2C_TK_STOP);
    enqueue_data(buffer, I2C_TK_START);
    enqueue_data(buffer, I2C_TK_ADDRR);
    for (int i = 0; i < 7; i++) {
        enqueue_data(buffer, I2C_TK_DATA);
    }
    enqueue_data(buffer, I2C_TK_STOP);
    enqueue_data(buffer, I2C_TK_END);

    ret = enqueue_used(&req_ring, req_buffer, data_index + 2);
    if (ret) {
        LOG_CLIENT_ERR("failed to enqueue request buffer!\n");
    }

    LOG_CLIENT("send read ack frame request\n");
    microkit_notify(DRIVER_CH);
}

void process_return_buffer() {
    LOG_CLIENT("processing return buffer\n");
    /* If we are here we must have something from the driver to process. */
    if (ring_empty(ret_ring.used_ring)) {
        LOG_CLIENT_ERR("return used ring is empty!\n");
        return;
    }

    uintptr_t ret_buffer = 0;
    unsigned int ret_buffer_len = 0;
    int err = dequeue_used(&ret_ring, &ret_buffer, &ret_buffer_len);
    if (err) {
        LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
        return;
    }

    LOG_CLIENT("return buffer 0x%lx with size 0x%lx\n", ret_buffer, ret_buffer_len);

    uint8_t *buffer = (uint8_t *) ret_buffer;

    LOG_CLIENT("RET_BUF_ERR is 0x%lx\n", buffer[RET_BUF_ERR]);
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

    LOG_CLIENT("return free ring size: 0x%lx\n", ring_size(ret_ring.free_ring));
    LOG_CLIENT("return used ring size: 0x%lx\n", ring_size(ret_ring.used_ring));
    LOG_CLIENT("request free ring size: 0x%lx\n", ring_size(req_ring.free_ring));
    LOG_CLIENT("request used ring size: 0x%lx\n", ring_size(req_ring.used_ring));

    uintptr_t req_buffer = 0;
    unsigned int buffer_len = 0;
    int ret = dequeue_free(&req_ring, &req_buffer, &buffer_len);
    if (ret) {
        microkit_dbg_puts("CLIENT|ERROR: could not dequeue free request buffer!\n");
        return;
    }

    // First dequeue shared ringbuffer buffer

    LOG_CLIENT("buffer is 0x%lx\n", req_buffer);
    uint8_t *buffer = (uint8_t *) req_buffer;
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
    size_t length = 0x2;
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

    enqueue_data(buffer, I2C_TK_STOP);
    enqueue_data(buffer, I2C_TK_END);

    LOG_CLIENT("finished setting up request\n");

    ret = enqueue_used(&req_ring, req_buffer, data_index + 2);
    if (ret) {
        LOG_CLIENT_ERR("failed to enqueue request buffer!\n");
    }

    LOG_CLIENT("enqueued, signalling driver!\n");
    microkit_notify(DRIVER_CH);
}

size_t length = 0;

void notified(microkit_channel ch) {
    switch (ch) {
        case DRIVER_CH:
            LOG_CLIENT("Got notification from driver!\n", ch);
            if (state == INIT) {
                process_return_buffer();
                read_ack_frame();
                state = CHECK_ACK_FRAME_RESPONSE;
            } else if (state == CHECK_ACK_FRAME_RESPONSE) {
                bool ready = check_ack_frame_response();
                if (ready) {
                    state = READ_RESPONSE_LENGTH;
                    get_response_length();
                }
                // } else {
                //     state = CHECK_ACK_FRAME_RESPONSE;
                //     read_ack_frame();
                // }
            } else if (state == READ_RESPONSE_LENGTH) {
                length = read_response_length();
                nack();
                state = REQUEST_READ_RESPONSE;
            } else if (state == REQUEST_READ_RESPONSE) {
                state = READ_RESPONSE;
                request_read_response(length);
            } else if (state == READ_RESPONSE) {
                read_firwmare_version();
            }
            break;
        default:
            LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}
