#include <stdint.h>

#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>

void init(void) {
    for (uint64_t i = 0; i < UINT64_MAX; i++) {
        if (i % 2 == 0) {
            microkit_msginfo iomuxc_msg = microkit_msginfo_new(0, 2);
        }

        sddf_timer_set_timeout(1, 2000000000);
        sddf_printf_("client hello #%lu\n", i);
    }
}

void notified(microkit_channel ch) {
}
