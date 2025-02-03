/*
 * Copyright 2021, Breakaway Consulting Pty. Ltd.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <serial_config.h>
#include <string.h>
#define TIMER 5
#define SERIAL_TX_CH 10
char *elf_a;

char *pd_code;

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;


void init(void)
{
    // serial_cli_queue_init_sys(microkit_name, NULL, NULL, NULL, &serial_tx_queue_handle, serial_tx_queue, serial_tx_data);
    // serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);
    // sddf_printf("Finished init'ing the swapper!\n");
}

void notified(microkit_channel ch)
{
    if (ch == 1) {
        // sddf_printf("Swapping out the elfs!: %d\n", ch);
        microkit_pd_stop(0);

        // uint64_t first_time = sddf_timer_time_now(TIMER);

        memcpy(pd_code, elf_a, 0x2000);


        // cache_clean_and_invalidate(pd_code, pd_code + 0x5000);
        seL4_ARM_VSpace_Unify_Instruction(3, 0x200000, 0x202000);
        seL4_Error err;
        seL4_UserContext ctxt = {0};
        ctxt.pc = 0x10000000;
        ctxt.sp = 0x0000010000000000;
        err = seL4_TCB_WriteRegisters(
                BASE_TCB_CAP + 0,
                seL4_True,
                0, /* No flags */
                2, /* writing 1 register */
                &ctxt
            );
        if (err != seL4_NoError) {
            microkit_dbg_puts("uh oh\n");
        }
        // uint64_t final_time = sddf_timer_time_now(TIMER) - first_time;

        // sddf_dprintf("This is the time: %ld\n", final_time);
    }
}

seL4_Bool fault(microkit_child child, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo)
{
    seL4_Word label = microkit_msginfo_get_label(msginfo);
    switch (label) {
        case seL4_Fault_VMFault: {
            microkit_dbg_puts("got vm fault\n");
            seL4_Word ip = seL4_GetMR(seL4_VMFault_IP);
            seL4_Word fault_addr = seL4_GetMR(seL4_VMFault_Addr);
            sddf_printf("This is the ip: %lx\nThis is the fault_addr: %lx\n", ip, fault_addr);
            break;
        }
        default:
            sddf_printf("unknown fault: %d\n", label);
            break;
    }
    return seL4_False;
}
