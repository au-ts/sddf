#include <stdint.h>

#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/pinctrl/client.h>

#include <libmicrokitco.h>

#define PINCTRL_CH 0
#define TIMER_CH 1

#define COSTACK_SIZE 8192

char co_stack[COSTACK_SIZE];
char co_control[sizeof(co_control_t)];

microkit_cothread_sem_t timer_expire_sem;

void run(void) {
    for (uint64_t i = 0; i < UINT64_MAX; i++) {
        if (i % 2 == 0) {
            // Connect UART1_TXD pad to the UART1 device
            sddf_pinctrl_set_mux(PINCTRL_CH, 0x238, 0x0);
        } else {
            // Connect UART1_TXD pad to the SPI device. You will not see the output for odd numbers
            sddf_pinctrl_set_mux(PINCTRL_CH, 0x238, 0x1);
        }
        
        sddf_printf_("client hello #%lu\n", i);
        sddf_timer_set_timeout(1, 1000000000ULL);

        microkit_cothread_semaphore_wait(&timer_expire_sem);
    }
}

void init(void) {
    microkit_cothread_init((co_control_t *) co_control, COSTACK_SIZE, co_stack);
    microkit_cothread_spawn(run, NULL);
    microkit_cothread_semaphore_init(&timer_expire_sem);
    microkit_cothread_yield();
}

void notified(microkit_channel ch) {
    if (ch == TIMER_CH) {
        microkit_cothread_semaphore_signal(&timer_expire_sem);
    }
}
