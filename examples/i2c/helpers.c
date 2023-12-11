#include <stdint.h>
#include <libco.h>

#include "i2c.h"
#include "printf.h"
#include "i2c-transport.h"

#define LOG_CLIENT(...) do{ printf("CLIENT|INFO: "); printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ printf("CLIENT|ERROR: "); printf(__VA_ARGS__); }while(0)

#define DRIVER_CH (0)

#define PN532_I2C_BUS_ADDRESS (0x48 >> 1)

#define PN532_PREAMBLE                (0x00)
#define PN532_STARTCODE1              (0x00)
#define PN532_STARTCODE2              (0xFF)
#define PN532_POSTAMBLE               (0x00)

#define PN532_HOSTTOPN532             (0xD4)
#define PN532_PN532TOHOST             (0xD5)

extern cothread_t t_event;
extern cothread_t t_main;

#define CLIENT_ID (0)

struct request {
    ring_handle_t *ring;
    uint8_t *buffer;
    /* Maximum amount of data the buffer can hold */
    size_t buffer_size;
    /* How many I2C tokens for processing we have enqueued */
    size_t data_offset_len;
};

struct response {
    uint8_t *buffer;
    size_t data_size;
    size_t read_idx;
};

/* @ivanv: when we finish dealing with a response, we should enqueue the buffer into the free ring */
void response_init(struct response *response, ring_handle_t *ring) {
    uintptr_t buffer = 0;
    unsigned int buffer_len = 0;
    int ret = dequeue_used(ring, &buffer, &buffer_len);
    if (ret) {
        LOG_CLIENT_ERR("response_init could not dequeue used response buffer!\n");
        return;
    }

    response->buffer = (uint8_t *) buffer;
    response->data_size = buffer_len;
    response->read_idx = 0;
}

uint8_t response_read(struct response *response) {
    if (response->read_idx >= response->data_size) {
        LOG_CLIENT_ERR("trying to read more data than exists in response (buffer: 0x%lx)\n", response->buffer);
        return 0;
    }

    uint8_t value = response->buffer[RET_BUF_DATA_OFFSET + response->read_idx];
    response->read_idx++;

    return value;
}

uint8_t response_read_idx(struct response *response, uint8_t idx) {
    if (idx >= response->data_size) {
        LOG_CLIENT_ERR("trying to read more data than exists in response (buffer: 0x%lx)\n", response->buffer);
        return 0;
    }

    uint8_t value = response->buffer[RET_BUF_DATA_OFFSET + idx];

    return value;
}

void request_init(struct request *req, ring_handle_t *ring, uint8_t client, uint8_t addr) {
    uintptr_t req_buffer = 0;
    unsigned int req_buffer_len = 0;
    int err = dequeue_free(ring, &req_buffer, &req_buffer_len);
    if (err) {
        LOG_CLIENT_ERR("could not dequeue free request buffer!\n");
        return;
    }

    req->ring = ring;
    req->buffer = (uint8_t *) req_buffer;
    req->buffer[REQ_BUF_CLIENT] = client;
    req->buffer[REQ_BUF_ADDR] = addr;
    req->data_offset_len = 0;
    req->buffer_size = req_buffer_len;
}

void request_add(struct request *req, uint8_t data) {
    size_t index = REQ_BUF_DATA_OFFSET + req->data_offset_len;
    if (index >= req->buffer_size) {
        LOG_CLIENT_ERR("request buffer is full (size is 0x%lx)\n", req->buffer_size);
        return;
    }
    req->buffer[index] = data;
    req->data_offset_len++;
}

void request_send(struct request *req) {
    /* Here we add two to account for the REQ_BUF_CLIENT and REQ_BUF_ADDR */
    int err = enqueue_used(req->ring, (uintptr_t) req->buffer, req->data_offset_len + 2);
    if (err) {
        LOG_CLIENT_ERR("failed to enqueue request buffer!\n");
    }

    microkit_notify(DRIVER_CH);
}

#define ACK_FRAME_SIZE (7)

uint8_t read_ack_frame() {
    /*
     * Read ACK frame has two parts, the first is to make the *request*
     * to read the frame. Then we need to process the response to that
     * request where we can actually check the data.
     */

    LOG_CLIENT("read_ack_frame: called\n");

    struct request req = {};
    request_init(&req, &req_ring, CLIENT_ID, PN532_I2C_BUS_ADDRESS);

    request_add(&req, I2C_TK_START);
    request_add(&req, I2C_TK_ADDRR);
    for (int i = 0; i < ACK_FRAME_SIZE; i++) {
        request_add(&req, I2C_TK_DATA);
    }
    request_add(&req, I2C_TK_DATA_END);
    request_add(&req, I2C_TK_STOP);
    request_add(&req, I2C_TK_END);

    request_send(&req);
    LOG_CLIENT("read_ack_frame: sent request\n");

    /* Now we need to wait for the return data of the ACK frame */
    co_switch(t_event);

    const uint8_t PN532_ACK[] = {0, 0, 0xFF, 0, 0xFF, 0};
    if (ring_size(ret_ring.used_ring) > 1) {
        LOG_CLIENT_ERR("return ring size is more than 1, actual size is %d\n", ring_size(ret_ring.used_ring));
        while (1) {};
    }
    struct response response = {};
    response_init(&response, &ret_ring);

    if (response_read(&response) & 1) {
        /* Minus one because the first byte is for the device ready status */
        for (int i = 0; i < ACK_FRAME_SIZE - 1; i++) {
            uint8_t value = response_read(&response);
            if (value != PN532_ACK[i]) {
                LOG_CLIENT_ERR("ACK malformed at index PN532_ACK[%d], value is %d!\n", i, value);
                while (1) {}
            }
        }
    } else {
        LOG_CLIENT_ERR("Device is not ready yet!\n");
        while (1) {};
    }

    return 0;
}

static void process_return_buffer() {
    uintptr_t ret_buffer = 0;
    unsigned int ret_buffer_len = 0;
    int err = dequeue_used(&ret_ring, &ret_buffer, &ret_buffer_len);
    if (err) {
        LOG_CLIENT_ERR("could not dequeue from return used ring!\n");
        return;
    }

    uint8_t *buffer = (uint8_t *) ret_buffer;

    if (buffer[RET_BUF_ERR] != I2C_ERR_OK) {
        LOG_CLIENT("Previous request failed where RET_BUF_ERR is 0x%lx\n", buffer[RET_BUF_ERR]);
    }
}

uint8_t write_command(uint8_t *header, uint8_t hlen, const uint8_t *body, uint8_t blen) {
    /* Setup command */

    /* First dequeue a fresh request buffer */
    struct request req = {};
    request_init(&req, &req_ring, CLIENT_ID, PN532_I2C_BUS_ADDRESS);
    request_add(&req, I2C_TK_START);
    request_add(&req, I2C_TK_ADDRW);

    request_add(&req, I2C_TK_DATA);
    request_add(&req, PN532_PREAMBLE);

    request_add(&req, I2C_TK_DATA);
    request_add(&req, PN532_STARTCODE1);

    request_add(&req, I2C_TK_DATA);
    request_add(&req, PN532_STARTCODE2);
    /* Put length of PN532 data */
    size_t length = hlen + blen + 1;
    request_add(&req, I2C_TK_DATA);
    request_add(&req, length);
    /* Put checksum of length of PN532 data */
    request_add(&req, I2C_TK_DATA);
    request_add(&req, ~length + 1);

    request_add(&req, I2C_TK_DATA);
    request_add(&req, PN532_HOSTTOPN532);

    uint8_t sum = PN532_HOSTTOPN532;
    for (int i = 0; i < hlen; i++) {
        sum += header[i];
        request_add(&req, I2C_TK_DATA);
        request_add(&req, header[i]);
    }

    for (int i = 0; i < blen; i++) {
        sum += body[i];
        request_add(&req, I2C_TK_DATA);
        request_add(&req, body[i]);
    }

    uint8_t checksum = ~sum + 1;
    request_add(&req, I2C_TK_DATA);
    request_add(&req, checksum);

    request_add(&req, I2C_TK_DATA);
    request_add(&req, PN532_POSTAMBLE);

    request_add(&req, I2C_TK_STOP);
    request_add(&req, I2C_TK_END);

    request_send(&req);

    /* Now we need to wait for the response */
    co_switch(t_event);

    process_return_buffer();

    return read_ack_frame();
}

uint8_t read_response_length() {
    struct request req = {};
    request_init(&req, &req_ring, CLIENT_ID, PN532_I2C_BUS_ADDRESS);

    request_add(&req, I2C_TK_START);
    request_add(&req, I2C_TK_ADDRR);
    /* @ivanv: This is slightly dodgy as I don't think we're actually reading
       6 bytes of data when we get the return buffer. However, this what the
       arduino code does so :shrug: */
    for (int i = 0; i < 6; i++) {
        request_add(&req, I2C_TK_DATA);
    }
    request_add(&req, I2C_TK_DATA_END);
    request_add(&req, I2C_TK_STOP);
    request_add(&req, I2C_TK_END);

    request_send(&req);

    co_switch(t_event);

    if (ring_size(ret_ring.used_ring) > 1) {
        LOG_CLIENT_ERR("return ring size is more than 1, actual size is %d\n", ring_size(ret_ring.used_ring));
        while (1) {};
    }
    struct response response = {};
    response_init(&response, &ret_ring);

    size_t length;
    if (response_read(&response) & 1) {
        length = response_read_idx(&response, 4);
    } else {
        LOG_CLIENT_ERR("device was not ready when reading the response length!\n");
        while (1) {};
    }

    /* Check nack */
    const uint8_t PN532_NACK[] = {0, 0, 0xFF, 0xFF, 0, 0};
    struct request nack_req = {};
    request_init(&nack_req, &req_ring, CLIENT_ID, PN532_I2C_BUS_ADDRESS);

    request_add(&nack_req, I2C_TK_START);
    request_add(&nack_req, I2C_TK_ADDRW);
    for (int i = 0; i < sizeof(PN532_NACK); i++) {
        request_add(&nack_req, I2C_TK_DATA);
        request_add(&nack_req, PN532_NACK[i]);
    }
    request_add(&nack_req, I2C_TK_STOP);
    request_add(&nack_req, I2C_TK_END);
    request_send(&nack_req);

    /* @ivanv: testing, shouldn't be necessary */
    co_switch(t_event);

    LOG_CLIENT("post nack ring_size of return ring: 0x%lx\n", ring_size(ret_ring.used_ring));

    return length;
}

void read_response(uint8_t *buffer, uint8_t buffer_len) {
    size_t length = read_response_length();

    struct request req = {};
    request_init(&req, &req_ring, CLIENT_ID, PN532_I2C_BUS_ADDRESS);

    size_t num_data_tokens = 6 + length + 2;

    request_add(&req, I2C_TK_START);
    request_add(&req, I2C_TK_ADDRR);

    if (num_data_tokens > req.buffer_size) {
        LOG_CLIENT_ERR("number of request data tokens (0x%lx) exceeds buffer size (0x%lx)\n", num_data_tokens, req.buffer_size);
        while (1) {}
    }

    for (int i = 0; i < num_data_tokens; i++) {
        request_add(&req, I2C_TK_DATA);
    }

    request_add(&req, I2C_TK_DATA_END);
    request_add(&req, I2C_TK_STOP);
    request_add(&req, I2C_TK_END);

    LOG_CLIENT("read_response: sent request of size %d\n", num_data_tokens);
    request_send(&req);

    co_switch(t_event);

    LOG_CLIENT("read_response: ret_ring.used_ring size is %d\n", ring_size(ret_ring.used_ring));
    struct response response1 = {};
    response_init(&response1, &ret_ring);
    struct response response2 = {};
    response_init(&response2, &ret_ring);

    if (!(response_read(&response2) & 1)) {
        LOG_CLIENT("reading response failed as device is not ready!\n");
        return;
    }

    // Read PREAMBLE
    if (response_read(&response2) != PN532_PREAMBLE) {
        LOG_CLIENT_ERR("read_response: PREAMBLE check failed\n");
        return;
    }
    // Read STARTCODE1
    if (response_read(&response2) != PN532_STARTCODE1) {
        LOG_CLIENT_ERR("read_response: STARTCODE1 check failed\n");
        return;
    }
    // Read STARTCODE2
    if (response_read(&response2) != PN532_STARTCODE2) {
        LOG_CLIENT_ERR("read_response: STARTCODE2 check failed\n");
        return;
    }
    // Read length
    size_t data_length = response_read(&response2);
    // LOG_CLIENT("data length is 0x%lx\n", data_length);
    if (data_length != length) {
        LOG_CLIENT_ERR("Received data_length of 0x%lx, was expecting 0x%lx\n", data_length, length);
        while (1) {}
    }
    // Read checksum of length
    response_read(&response2);
    // Read response command
    response_read(&response2);

    response_read(&response2);
    // Read command data
    if (data_length > buffer_len) {
        LOG_CLIENT_ERR("returned data length (0x%lx) greater than user-provided buffer length (0x%lx)\n", data_length, buffer_len);
    }
    for (int i = 0; i < data_length; i++) {
        buffer[i] = response_read(&response2);
    }
    // Read checksum of data
    response_read(&response2);
    // Read postamble
    response_read(&response2);
}
