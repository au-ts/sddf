#include <stdint.h>
#include <sel4cp.h>
#include "timer.h"

static char
hexchar(unsigned int v)
{
    return v < 10 ? '0' + v : ('a' - 10) + v;
}

static void
puthex64(uint64_t val)
{
    char buffer[16 + 3];
    buffer[0] = '0';
    buffer[1] = 'x';
    buffer[16 + 3 - 1] = 0;
    for (unsigned i = 16 + 1; i > 1; i--) {
        buffer[i] = hexchar(val & 0xf);
        val >>= 4;
    }
    sel4cp_dbg_puts(buffer);
}

void
notified(sel4cp_channel ch) 
{
    sel4cp_dbg_puts("Got a timeout!\n");
    set_timeout(NS_IN_S);
}

void
init(void)
{
    // lets get the time!
    uint64_t time = time_now() / NS_IN_MS;
    sel4cp_dbg_puts("The time now is: ");
    puthex64(time);
    sel4cp_dbg_puts("\n");

    // lets set a timeout
    sel4cp_dbg_puts("Setting a time out for 1 seconds time\n");
    set_timeout(NS_IN_S);
}
