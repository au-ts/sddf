#include <microkit.h>

void _sddf_putchar(char character)
{
    microkit_dbg_putc(character);
}
