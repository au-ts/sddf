/*
 * Copyright 2021, Breakaway Consulting Pty. Ltd.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>

char *elf_a;

char *pd_code;

void init(void)
{
}

void notified(microkit_channel ch)
{
    microkit_dbg_puts("Swapping out the elfs!\n");
    microkit_pd_stop(0);
    uint64_t elf_hash = 0;

    for (int i = 0; i < 0x5000; i++) {
        pd_code[i] = elf_a[i];
        elf_hash += elf_a[i];
    }

    sddf_dprintf("This is the total of the elf hash: %lld\n", elf_hash);

    for (int i = 0; i < 10; i++) {
        sddf_dprintf("This is %d of pd_code: 0x%x\n", i, pd_code[i]);
    }

    cache_clean_and_invalidate(pd_code, pd_code + 0x5000);
    seL4_ARM_VSpace_Unify_Instruction(3, 0x200000, 0x205000);
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
}

seL4_Bool fault(microkit_child child, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo)
{
    seL4_Word label = microkit_msginfo_get_label(msginfo);
    switch (label) {
        case seL4_Fault_VMFault: {
            microkit_dbg_puts("got vm fault\n");
            seL4_Word ip = seL4_GetMR(seL4_VMFault_IP);
            seL4_Word fault_addr = seL4_GetMR(seL4_VMFault_Addr);
            sddf_dprintf("This is the ip: %lx\nThis is the fault_addr: %lx\n", ip, fault_addr);
            break;
        }
        default:
            sddf_dprintf("unknown fault: %d\n", label);
            break;
    }
    return seL4_False;
}
