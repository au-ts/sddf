#include <microkit.h>

void notified(microkit_channel ch) {};

void init() {
    microkit_dbg_puts("hello!\n");
}
