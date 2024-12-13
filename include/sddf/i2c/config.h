#include <microkit.h>

#define SDDF_I2C_MAX_CLIENTS (MICROKIT_MAX_CHANNELS - 1)

typedef struct i2c_driver_config {
    uint64_t bus_num;
    void *request_region;
    void *response_region;
    void *data_region;
    uint8_t virt_id;
} i2c_driver_config_t;

typedef struct i2c_virt_client_config {
    void *request_queue;
    void *response_queue;
    uint64_t driver_data_offset;
    uint64_t data_size;
} i2c_virt_client_config_t;

typedef struct i2c_virt_config {
    void *driver_request_queue;
    void *driver_response_queue;
    uint8_t driver_id;
    uint64_t num_clients;
    i2c_virt_client_config_t clients[SDDF_I2C_MAX_CLIENTS];
} i2c_virt_config_t;

typedef struct i2c_client_config {
    void *request_region;
    void *response_region;
    void *data_region;
    uint8_t virt_id;
} i2c_client_config_t;
