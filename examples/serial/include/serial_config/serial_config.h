#pragma once

#include <microkit.h>
#include <sddf/serial/queue.h>

#define NUM_CLIENTS 2

#define CLI0_NAME "serial_server0"
#define CLI1_NAME "serial_server1"
#define VIRT_RX_NAME "virt_rx"
#define VIRT_TX_NAME "virt_tx"
#define DRIVER_NAME "uart"

#define DATA_REGION_SIZE                    0x200000

#define TX_QUEUE_SIZE_CLI0                   512
#define TX_QUEUE_SIZE_CLI1                   512
#define TX_QUEUE_SIZE_DRIV                   512

#define TX_DATA_REGION_SIZE_DRIV            DATA_REGION_SIZE
#define TX_DATA_REGION_SIZE_CLI0            DATA_REGION_SIZE
#define TX_DATA_REGION_SIZE_CLI1            DATA_REGION_SIZE

_Static_assert(TX_DATA_REGION_SIZE_DRIV >= TX_QUEUE_SIZE_DRIV * BUFFER_SIZE, "Driver TX data region size must fit Driver TX buffers");
_Static_assert(TX_DATA_REGION_SIZE_CLI0 >= TX_QUEUE_SIZE_CLI0 * BUFFER_SIZE, "Client0 TX data region size must fit Client0 TX buffers");
_Static_assert(TX_DATA_REGION_SIZE_CLI1 >= TX_QUEUE_SIZE_CLI1 * BUFFER_SIZE, "Client1 TX data region size must fit Client1 TX buffers");

#define RX_QUEUE_SIZE_DRIV                   512
#define RX_QUEUE_SIZE_CLI0                   512
#define RX_QUEUE_SIZE_CLI1                   512

#define RX_DATA_REGION_SIZE_DRIV            DATA_REGION_SIZE
#define RX_DATA_REGION_SIZE_CLI0            DATA_REGION_SIZE
#define RX_DATA_REGION_SIZE_CLI1            DATA_REGION_SIZE

_Static_assert(RX_DATA_REGION_SIZE_DRIV >= RX_QUEUE_SIZE_DRIV * BUFFER_SIZE, "Driver RX data region size must fit Driver RX buffers");
_Static_assert(RX_DATA_REGION_SIZE_CLI0 >= RX_QUEUE_SIZE_CLI0 * BUFFER_SIZE, "Client0 RX data region size must fit Client0 RX buffers");
_Static_assert(RX_DATA_REGION_SIZE_CLI1 >= RX_QUEUE_SIZE_CLI1 * BUFFER_SIZE, "Client1 RX data region size must fit Client1 RX buffers");

static inline bool __str_match(const char *s0, const char *s1)
{
    while (*s0 != '\0' && *s1 != '\0' && *s0 == *s1) {
        s0++, s1++;
    }
    return *s0 == *s1;
}

static inline void cli_queue_init_sys(char *pd_name, serial_queue_handle_t *rx_queue, uintptr_t rx_free, uintptr_t rx_active,
                                serial_queue_handle_t *tx_queue, uintptr_t tx_free, uintptr_t tx_active)
{
    if (__str_match(pd_name, CLI0_NAME)) {
        serial_queue_init(rx_queue, (serial_queue_t *) rx_free, (serial_queue_t *) rx_active, RX_QUEUE_SIZE_CLI0);
        serial_queue_init(tx_queue, (serial_queue_t *) tx_free, (serial_queue_t *) tx_active, TX_QUEUE_SIZE_CLI0);
    } else if (__str_match(pd_name, CLI1_NAME)) {
        serial_queue_init(rx_queue, (serial_queue_t *) rx_free, (serial_queue_t *) rx_active, RX_QUEUE_SIZE_CLI1);
        serial_queue_init(tx_queue, (serial_queue_t *) tx_free, (serial_queue_t *) tx_active, TX_QUEUE_SIZE_CLI1);
    }
}

static inline void virt_queue_init_sys(char *pd_name, serial_queue_handle_t *cli_queue, uintptr_t cli_free, uintptr_t cli_active)
{
    if (__str_match(pd_name, VIRT_RX_NAME)) {
        serial_queue_init(cli_queue, (serial_queue_t *) cli_free, (serial_queue_t *) cli_active, RX_QUEUE_SIZE_CLI0);
        serial_queue_init(&cli_queue[1], (serial_queue_t *) (cli_free + 2 * DATA_REGION_SIZE), (serial_queue_t *) (cli_active + 2 * DATA_REGION_SIZE), RX_QUEUE_SIZE_CLI1);
    } else if (__str_match(pd_name, VIRT_TX_NAME)) {
        serial_queue_init(cli_queue, (serial_queue_t *) cli_free, (serial_queue_t *) cli_active, TX_QUEUE_SIZE_CLI0);
        serial_queue_init(&cli_queue[1], (serial_queue_t *) (cli_free + 2 * DATA_REGION_SIZE), (serial_queue_t *) (cli_active + 2 * DATA_REGION_SIZE), TX_QUEUE_SIZE_CLI1);
    }
}