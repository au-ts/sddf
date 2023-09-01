// i am silly



#include <sel4cp.h>
#include "printf.h"

void _putchar(char c) {
    sel4cp_dbg_putc(c);
}

void notified(sel4cp_channel ch) {
    // Server has done its magic
    sel4cp_dbg_puts("fool: notified\n");

    seL4_MessageInfo_t m = sel4cp_msginfo_new(0, 0);
    volatile seL4_MessageInfo_t response = sel4cp_ppcall(2, m);
    sel4cp_dbg_puts("fool: response received\n");
    uint32_t val[7];
    for (int i = 0; i < 7; i++) {
        val[i] = sel4cp_mr_get(i);
    }
    for (int i = 0; i < 7; i++) {
        printf("\t0x%x", val[i]);
    }
    printf("\n");
    sel4cp_notify(2);
}

void init(void) {
    sel4cp_dbg_puts("fool: init\n");

    // Prompt server to poll
    sel4cp_notify(2);

}


