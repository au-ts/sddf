/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/util/pancake_common.h>
#include "virt_rx.h"

/* renamed from the init() function of the C driver */
extern void c_init(void);

void init(void)
{
    c_init();

    init_pancake_mem();

    uintptr_t *pnk_mem = (uintptr_t *)cml_heap;

    pnk_mem[0] = (uintptr_t)&rx_queue_handle_drv;
    pnk_mem[1] = (uintptr_t)&rx_queue_handle_cli[0];
    pnk_mem[2] = (uintptr_t)&next_client[0];
    pnk_mem[3] = config.switch_char;
    pnk_mem[4] = config.terminate_num_char;
    pnk_mem[5] = config.num_clients;
    pnk_mem[6] = config.driver.id;
    pnk_mem[7] = (uintptr_t)&config.clients[0];

    cml_main();
}
