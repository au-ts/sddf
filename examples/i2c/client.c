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
