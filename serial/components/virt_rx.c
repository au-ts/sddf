/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/util/string.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".serial_virt_rx_config"))) serial_virt_rx_config_t config;

serial_queue_handle_t rx_queue_handle_drv;
serial_queue_handle_t rx_queue_handle_cli[SDDF_SERIAL_MAX_CLIENTS];

#define MAX_CLI_BASE_10 4
typedef enum mode {normal, switched, number} mode_t;

mode_t current_mode = normal;
uint32_t current_client = 0;
char next_client[MAX_CLI_BASE_10 + 1];
uint8_t next_client_index;

void reset_state(void)
{
    sddf_memset(next_client, '\0', MAX_CLI_BASE_10 + 1);
    next_client_index = 0;
    current_mode = normal;
}

void rx_return(void)
{
    bool transferred = false;
    uint32_t local_tail = rx_queue_handle_cli[current_client].queue->tail;
    char c = '\0';
    while (!serial_dequeue(&rx_queue_handle_drv, &c)) {
        switch (current_mode) {
        case normal:
            if (c == config.switch_char) {
                current_mode = switched;
            } else {
                if (!serial_enqueue_local(&rx_queue_handle_cli[current_client], &local_tail, c)) {
                    transferred = true;
                }
            }
            break;
        case switched:
            if (sddf_isdigit(c)) {
                next_client[next_client_index] = c;
                next_client_index++;
                current_mode = number;
            } else {
                if (c == config.switch_char) {
                    if (!serial_enqueue_local(&rx_queue_handle_cli[current_client], &local_tail, c)) {
                        transferred = true;
                    }
                } else {
                    sddf_dprintf("VIRT_RX|LOG: User entered an invalid digit %c\n", c);
                }
                reset_state();
            }
            break;
        default:
            if (c == config.terminate_num_char) {
                int input_number = sddf_atoi(next_client);
                if (input_number >= 0 && input_number < config.num_clients) {
                    if (transferred) {
                        serial_update_shared_tail(&rx_queue_handle_cli[current_client], local_tail);
                        sddf_notify(config.clients[current_client].id);
                    }
                    current_client = (uint32_t)input_number;
                    local_tail = rx_queue_handle_cli[current_client].queue->tail;
                    transferred = false;
                    sddf_dprintf("VIRT_RX|LOG: switching to client %d\n", input_number);
                } else {
                    sddf_dprintf("VIRT_RX|LOG: User requested to switch to an invalid client %d\n", input_number);
                }
                reset_state();
            } else if (next_client_index < MAX_CLI_BASE_10 && sddf_isdigit((int)c)) {
                next_client[next_client_index] = c;
                next_client_index++;
            } else {
                sddf_dprintf("VIRT_RX|LOG: User entered too many (%u < %u) or invalid digit (%c)\n",
                             next_client_index + 1, MAX_CLI_BASE_10, c);
                reset_state();
            }
            break;
        }
    }

    serial_update_shared_tail(&rx_queue_handle_cli[current_client], local_tail);
    if (!serial_queue_full(&rx_queue_handle_drv, rx_queue_handle_drv.queue->tail)
        && serial_require_consumer_signal(&rx_queue_handle_drv)) {
        serial_cancel_consumer_signal(&rx_queue_handle_drv);
        sddf_notify(config.driver.id);
    }

    if (transferred) {
        sddf_notify(config.clients[current_client].id);
    }
}

void init(void)
{
    assert(serial_config_check_magic(&config));

    serial_queue_init(&rx_queue_handle_drv, config.driver.queue.vaddr, config.driver.data.size,
                      config.driver.data.vaddr);
    for (uint64_t i = 0; i < config.num_clients; i++) {
        serial_queue_init(&rx_queue_handle_cli[i], config.clients[i].queue.vaddr, config.clients[i].data.size,
                          config.clients[i].data.vaddr);
    }
}

void notified(sddf_channel ch)
{
    if (ch == config.driver.id) {
        rx_return();
    } else {
        sddf_dprintf("VIRT_RX|LOG: received notification on unexpected channel: %u\n", ch);
    }
}
