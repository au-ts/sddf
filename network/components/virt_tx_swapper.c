/*
 * Copyright 2021, Breakaway Consulting Pty. Ltd.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>

char *elf_a;

char *pd_code;

void init(void)
{
    microkit_dbg_puts("ELF TESTER starting\n");
}

int pd = 0;

void notified(microkit_channel ch)
{
    microkit_dbg_puts("Swapping out the elfs!\n");
    microkit_pd_stop(0);

    for (int i = 0; i < 0x4000; i++) {
        pd_code[i] = 0;
    }

    microkit_dbg_puts("Finished copying the elf\n");

    seL4_Error err;
    seL4_UserContext ctxt = {0};
    ctxt.pc = 0x200000;
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
}

seL4_Bool fault(microkit_child child, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo)
{
    seL4_Word label = microkit_msginfo_get_label(msginfo);
    switch (label) {
        case seL4_Fault_VMFault: {
            microkit_dbg_puts("got vm fault\n");
            seL4_Word ip = seL4_GetMR(seL4_VMFault_IP);
            seL4_Word fault_addr = seL4_GetMR(seL4_VMFault_Addr);
            break;
        }
        default:
            microkit_dbg_puts("unknown\n");
            break;
    }
    return seL4_False;
}
