#include <microkit.h>

void _putchar(char character)
{
    microkit_dbg_putc(character);
}
