#pragma once

#include <microkit.h>
#include <sddf/util/string.h>
#include <sddf/serial/queue.h>
#include <stdint.h>

/* Number of clients that can be connected to the serial server. */
#define SERIAL_NUM_CLIENTS 8

/* Only support transmission and not receive. */
#define SERIAL_TX_ONLY 1

/* Associate a colour with each client's output. */
#define SERIAL_WITH_COLOUR 1

/* Control character to switch input stream - ctrl \. To input character input twice. */
#define SERIAL_SWITCH_CHAR 28

/* Control character to terminate client number input. */
#define SERIAL_TERMINATE_NUM '\r'

/* Default baud rate of the uart device */
#define UART_DEFAULT_BAUD 115200

#define SERIAL_CLI0_NAME "client0"
#define SERIAL_CLI1_NAME "client1"
#define SERIAL_CLI2_NAME "bench"
#define SERIAL_CLI3_NAME "eth"
#define SERIAL_CLI4_NAME "net_virt_rx"
#define SERIAL_CLI5_NAME "copy0"
#define SERIAL_CLI6_NAME "net_virt_tx"
#define SERIAL_CLI7_NAME "copy1"
#define SERIAL_VIRT_RX_NAME "serial_virt_rx"
#define SERIAL_VIRT_TX_NAME "serial_virt_tx"
#define SERIAL_DRIVER_NAME "uart"

#define SERIAL_QUEUE_SIZE                          0x1000
#define SERIAL_DATA_REGION_SIZE                    0x2000

#define SERIAL_TX_DATA_REGION_SIZE_DRIV            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI0            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI1            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI2            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI3            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI4            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI5            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI6            SERIAL_DATA_REGION_SIZE
#define SERIAL_TX_DATA_REGION_SIZE_CLI7            SERIAL_DATA_REGION_SIZE

#define SERIAL_RX_DATA_REGION_SIZE_DRIV            SERIAL_DATA_REGION_SIZE
#define SERIAL_RX_DATA_REGION_SIZE_CLI0            SERIAL_DATA_REGION_SIZE
#define SERIAL_RX_DATA_REGION_SIZE_CLI1            SERIAL_DATA_REGION_SIZE

#define SERIAL_MAX_TX_DATA_SIZE MAX(SERIAL_TX_DATA_REGION_SIZE_DRIV, MAX(SERIAL_TX_DATA_REGION_SIZE_CLI0, MAX(SERIAL_TX_DATA_REGION_SIZE_CLI1, SERIAL_TX_DATA_REGION_SIZE_CLI2)))
#define SERIAL_MAX_RX_DATA_SIZE MAX(SERIAL_RX_DATA_REGION_SIZE_DRIV, MAX(SERIAL_RX_DATA_REGION_SIZE_CLI0, SERIAL_RX_DATA_REGION_SIZE_CLI1))
#define SERIAL_MAX_DATA_SIZE MAX(SERIAL_MAX_TX_DATA_SIZE, SERIAL_MAX_RX_DATA_SIZE)
_Static_assert(SERIAL_MAX_DATA_SIZE < UINT32_MAX,
               "Data regions must be smaller than UINT32 max to correctly use queue data structure.");

static inline void serial_cli_queue_init_sys(char *pd_name, serial_queue_handle_t *rx_queue_handle,
                                             serial_queue_t *rx_queue,
                                             char *rx_data, serial_queue_handle_t *tx_queue_handle, serial_queue_t *tx_queue, char *tx_data)
{
    if (!sddf_strcmp(pd_name, SERIAL_CLI0_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI0, tx_data);
    } else if (!sddf_strcmp(pd_name, SERIAL_CLI1_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI1, tx_data);
    } else if (!sddf_strcmp(pd_name, SERIAL_CLI2_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI2, tx_data);
    } else if (!sddf_strcmp(pd_name, SERIAL_CLI3_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI3, tx_data);
    } else if (!sddf_strcmp(pd_name, SERIAL_CLI4_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI4, tx_data);
    } else if (!sddf_strcmp(pd_name, SERIAL_CLI5_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI5, tx_data);
    } else if (!sddf_strcmp(pd_name, SERIAL_CLI6_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI6, tx_data);
    } else if (!sddf_strcmp(pd_name, SERIAL_CLI7_NAME)) {
        serial_queue_init(tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_SIZE_CLI7, tx_data);
    }
}

static inline void serial_virt_queue_init_sys(char *pd_name, serial_queue_handle_t *cli_queue_handle,
                                              uintptr_t cli_queue, uintptr_t cli_data)
{
    if (!sddf_strcmp(pd_name, SERIAL_VIRT_RX_NAME)) {
        serial_queue_init(cli_queue_handle, (serial_queue_t *) cli_queue, SERIAL_RX_DATA_REGION_SIZE_CLI0, (char *)cli_data);
        serial_queue_init(&cli_queue_handle[1], (serial_queue_t *)(cli_queue + SERIAL_QUEUE_SIZE),
                          SERIAL_RX_DATA_REGION_SIZE_CLI1, (char *)(cli_data + SERIAL_RX_DATA_REGION_SIZE_CLI0));
    } else if (!sddf_strcmp(pd_name, SERIAL_VIRT_TX_NAME)) {
        void *queue_data_pointer = (void *)cli_data;
        serial_queue_init(cli_queue_handle, (serial_queue_t *) cli_queue, SERIAL_TX_DATA_REGION_SIZE_CLI0, (char *)queue_data_pointer);
        queue_data_pointer += SERIAL_TX_DATA_REGION_SIZE_CLI0;
        serial_queue_init(&cli_queue_handle[1], (serial_queue_t *)(cli_queue + SERIAL_QUEUE_SIZE),
                          SERIAL_TX_DATA_REGION_SIZE_CLI1, (char *)queue_data_pointer);
        queue_data_pointer += SERIAL_TX_DATA_REGION_SIZE_CLI1;
        serial_queue_init(&cli_queue_handle[2], (serial_queue_t *)(cli_queue + 2 * SERIAL_QUEUE_SIZE),
                          SERIAL_TX_DATA_REGION_SIZE_CLI2, (char *)queue_data_pointer);
        queue_data_pointer += SERIAL_TX_DATA_REGION_SIZE_CLI2;
        serial_queue_init(&cli_queue_handle[3], (serial_queue_t *)(cli_queue + 3 * SERIAL_QUEUE_SIZE),
                          SERIAL_TX_DATA_REGION_SIZE_CLI3, (char *)queue_data_pointer);
        queue_data_pointer += SERIAL_TX_DATA_REGION_SIZE_CLI3;
        serial_queue_init(&cli_queue_handle[4], (serial_queue_t *)(cli_queue + 4 * SERIAL_QUEUE_SIZE),
                          SERIAL_TX_DATA_REGION_SIZE_CLI4, (char *)queue_data_pointer);
        queue_data_pointer += SERIAL_TX_DATA_REGION_SIZE_CLI4;
        serial_queue_init(&cli_queue_handle[5], (serial_queue_t *)(cli_queue + 5 * SERIAL_QUEUE_SIZE),
                          SERIAL_TX_DATA_REGION_SIZE_CLI5, (char *)queue_data_pointer);
        queue_data_pointer += SERIAL_TX_DATA_REGION_SIZE_CLI5;
        serial_queue_init(&cli_queue_handle[6], (serial_queue_t *)(cli_queue + 6 * SERIAL_QUEUE_SIZE),
                          SERIAL_TX_DATA_REGION_SIZE_CLI6, (char *)queue_data_pointer);
        queue_data_pointer += SERIAL_TX_DATA_REGION_SIZE_CLI6;
        serial_queue_init(&cli_queue_handle[7], (serial_queue_t *)(cli_queue + 7 * SERIAL_QUEUE_SIZE),
                          SERIAL_TX_DATA_REGION_SIZE_CLI7, (char *)queue_data_pointer);
    }
}

#if SERIAL_WITH_COLOUR
static inline void serial_channel_names_init(char **client_names)
{
    client_names[0] = SERIAL_CLI0_NAME;
    client_names[1] = SERIAL_CLI1_NAME;
    client_names[2] = SERIAL_CLI2_NAME;
    client_names[3] = SERIAL_CLI3_NAME;
    client_names[4] = SERIAL_CLI4_NAME;
    client_names[5] = SERIAL_CLI5_NAME;
    client_names[6] = SERIAL_CLI6_NAME;
    client_names[7] = SERIAL_CLI7_NAME;
}
#endif