#include <microkit.h>

void
init(void)
{
    // generic_timer_enable();
    // microkit_dbg_puts("");
}

void
notified(microkit_channel ch)
{
}

seL4_MessageInfo_t
protected(microkit_channel ch, microkit_msginfo msginfo)
{
    return microkit_msginfo_new(0, 0);
}
