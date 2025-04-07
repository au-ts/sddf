/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>

typedef struct ip_collector_config {
    void *ip_pool_vaddr;
    uint8_t num_clients;
} ip_collector_config_t;

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".ip_collector_config"))) ip_collector_config_t config;

serial_queue_handle_t serial_tx_queue_handle;

void init(void)
{
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    sddf_timer_set_timeout(timer_config.driver_id, 50 * NS_IN_MS);
}

void notified(microkit_channel ch)
{
    if (ch == timer_config.driver_id) {
        uint32_t cnt = 0;
        for (int i = 0; i < config.num_clients; i++) {
            char *ip_vaddr = (char *)(config.ip_pool_vaddr + 0x1000 * i);
            if (ip_vaddr[0]) {
                cnt += 1;
            }
        }
        if (cnt == config.num_clients) {
            for (int i = 0; i < config.num_clients; i++) {
                char *ip_vaddr = (char *)(config.ip_pool_vaddr + 0x1000 * i);
                sddf_printf("IP address for client%d is: %s\n", i, ip_vaddr);
            }
        } else {
            sddf_timer_set_timeout(timer_config.driver_id, 50 * NS_IN_MS);
        }
    }
}
