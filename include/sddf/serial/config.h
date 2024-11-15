
#include <microkit.h>

#define SDDF_SERIAL_MAX_CLIENTS (MICROKIT_MAX_CHANNELS - 1)
#define SDDF_SERIAL_BEGIN_STR_MAX_LEN 128

typedef struct serial_driver_config {
    void *rx_queue;
    void *tx_queue;
    void *rx_data;
    void *tx_data;
    uint64_t rx_capacity;
    uint64_t tx_capacity;
    uint64_t default_baud;
    bool rx_enabled;
    uint8_t rx_id;
    uint8_t tx_id;
} serial_driver_config_t;

typedef struct serial_virt_rx_client_config {
    void *rx_queue;
    void *rx_data;
    uint64_t rx_capacity;
    uint8_t id;
} serial_virt_rx_client_config_t;

typedef struct serial_virt_rx_config {
    void *rx_queue_drv;
    void *rx_data_drv;
    uint64_t rx_capacity_drv;
    char switch_char;
    char terminate_num_char;
    uint64_t num_clients;
    uint8_t driver_id;
    serial_virt_rx_client_config_t clients[SDDF_SERIAL_MAX_CLIENTS];
} serial_virt_rx_config_t;

typedef struct serial_virt_tx_client_config {
    char name[MICROKIT_PD_NAME_LENGTH];
    void *tx_queue;
    void *tx_data;
    uint64_t tx_capacity;
    uint8_t id;
} serial_virt_tx_client_config_t;

typedef struct serial_virt_tx_config {
    void *tx_queue_drv;
    void *tx_data_drv;
    uint64_t tx_capacity_drv;
    char begin_str[SDDF_SERIAL_BEGIN_STR_MAX_LEN];
    uint64_t begin_str_len;
    bool enable_colour;
    bool enable_rx;
    uint64_t num_clients;
    uint8_t driver_id;
    serial_virt_tx_client_config_t clients[SDDF_SERIAL_MAX_CLIENTS];
} serial_virt_tx_config_t;

typedef struct serial_client_config {
    void *rx_queue;
    void *rx_data;
    uint64_t rx_capacity;

    void *tx_queue;
    void *tx_data;
    uint64_t tx_capacity;

    uint8_t rx_id;
    uint8_t tx_id;
} serial_client_config_t;
