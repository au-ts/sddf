/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <sddf/util/pancake_common.h>
#include <sddf/util/util.h>
#include "virt_tx.h"

/* renamed from the init() function of the C driver */
extern void c_init(void);

bool notify_client[SDDF_SERIAL_MAX_CLIENTS];

void init(void)
{
    c_init();

    init_pancake_mem();

    uintptr_t *pnk_mem = (uintptr_t *)cml_heap;

    pnk_mem[0] = (uintptr_t)&tx_queue_handle_drv;
    pnk_mem[1] = (uintptr_t)&tx_queue_handle_cli[0];
    pnk_mem[2] = (uintptr_t)&tx_pending.clients_pending[0];
    pnk_mem[3] = (uintptr_t)&tx_pending.queue[0];
    pnk_mem[4] = config.enable_colour;
    pnk_mem[5] = (uintptr_t)&colours[0];
    pnk_mem[6] = ARRAY_SIZE(colours);
    pnk_mem[7] = (uintptr_t)COLOUR_END;
    pnk_mem[8] = (uintptr_t)&notify_client[0];
    pnk_mem[9] = config.driver.id;
    pnk_mem[10] = config.num_clients;
    pnk_mem[11] = (uintptr_t)&config.clients[0];

    cml_main();
}
