#include <microkit.h>

#define SDDF_NET_MAX_CLIENTS (MICROKIT_MAX_CHANNELS - 1)

typedef struct net_driver_config {
    uintptr_t hw_ring_buffer_vaddr;
    uintptr_t hw_ring_buffer_paddr;
    void *rx_free;
    void *rx_active;
    void *tx_free;
    void *tx_active;
    size_t rx_capacity;
    size_t tx_capacity;

    uint8_t tx_id;
    uint8_t rx_id;
} net_driver_config_t;

typedef struct net_virt_tx_client_config {
    void *free;
    void *active;
    size_t capacity;
    uint8_t id;
    uintptr_t buffer_data_region_vaddr;
    uintptr_t buffer_data_region_paddr;
} net_virt_tx_client_config_t;

typedef struct net_virt_tx_config {
    void *free_drv;
    void *active_drv;
    size_t capacity_drv;
    uint8_t drv_id;
    uint8_t num_clients;
    net_virt_tx_client_config_t clients[SDDF_NET_MAX_CLIENTS];
} net_virt_tx_config_t;

typedef struct net_virt_rx_config_client {
    void *free;
    void *active;
    uint64_t capacity;
    uint8_t mac_addr[6];
    uint8_t client_id;
} net_virt_rx_config_client_t;

typedef struct net_virt_rx_config {
    void *free_drv;
    void *active_drv;
    uint64_t capacity_drv;
    uintptr_t buffer_data_vaddr;
    uintptr_t buffer_data_paddr;
    // The system designer must allocate a buffer metadata region for internal
    // use by the RX virtualiser. The size of this region must be at least
    // 4*drv_queue_capacity. It must be mapped R-W and zero-initialised.
    void *buffer_metadata;
    uint8_t driver_id;
    uint8_t num_clients;
    net_virt_rx_config_client_t clients[SDDF_NET_MAX_CLIENTS];
} net_virt_rx_config_t;

typedef struct net_copy_config {
 	void *virt_free;
 	void *virt_active;
 	size_t virt_capacity;
 	void *cli_free;
 	void *cli_active;
 	size_t cli_capacity;
 	uintptr_t virt_data;
 	uintptr_t cli_data;
 
 	uint8_t virt_id;
 	uint8_t cli_id;
} net_copy_config_t;