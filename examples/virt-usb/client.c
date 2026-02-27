#include <sddf/util/printf.h>
#include <os/sddf.h>

void init(void)
{
    sddf_printf("client init\n");
}

void notified(sddf_channel ch)
{
    sddf_printf("client notified?\n");
}
