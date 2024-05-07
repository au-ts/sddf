#pragma once

#include <stdint.h>

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("I2C DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("I2C DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

/* I2C Feature Flags */
#define VIRTIO_I2C_F_ZERO_LENGTH_REQUEST 0

/* I2C Message Flags */
#define VIRTIO_I2C_FLAGS_FAIL_NEXT 0
#define VIRTIO_I2C_FLAGS_M_RD 1
#define VIRTIO_I2C_MSG_ERR 1

typedef struct _virtio_i2c_state {
    uintptr_t curr_data;
    uint32_t len;
} virtio_i2c_state_t;

struct virtio_i2c_out_hdr {
    uint16_t addr;
    uint16_t padding;
    uint32_t flags;
};

struct virtio_i2c_in_hdr {
    uint8_t status;
};

struct virtio_i2c_req {
    struct virtio_i2c_out_hdr out_hdr;
    /* TODO: Figure out how this zero length copy fits in. */
    uint8_t *buf;
    struct virtio_i2c_in_hdr in_hdr;
};