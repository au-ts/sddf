/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/util/pancake_common.h>
#include <uart.h>

/* renamed from the init() function of the C driver */
extern void c_init(void);

void init(void)
{
    c_init();

    init_pancake_mem();

    uintptr_t *pnk_mem = (uintptr_t *)cml_heap;

    pnk_mem[0] = (uintptr_t)uart_base;
    pnk_mem[1] = device_resources.irqs[0].id;
    pnk_mem[2] = config.rx.id;
    pnk_mem[3] = config.tx.id;
    pnk_mem[4] = (uintptr_t)&rx_queue_handle;
    pnk_mem[5] = (uintptr_t)&tx_queue_handle;

    cml_main();
}
