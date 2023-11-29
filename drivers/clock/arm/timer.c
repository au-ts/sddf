#include <microkit.h>
#include <stdint.h>
#include "coproc.h"
#include "frequency.h"
#include "util.h"
#include "printf.h"

#define GENERIC_TIMER_ENABLE BIT(0)
#define GENERIC_TIMER_IMASK  BIT(1)
#define GENERIC_TIMER_STATUS BIT(2)
/* Tested to work on ARM A53's */
#define GENERIC_TIMER_PCNT_IRQ 30

static inline uint64_t generic_timer_get_ticks(void)
{
    uint64_t time;
    COPROC_READ_64(CNTPCT, time);
    return time;
}

static inline void generic_timer_set_compare(uint64_t ticks)
{
    COPROC_WRITE_64(CNTP_CVAL, ticks);
}

static inline uint32_t generic_timer_get_freq(void)
{
    uintptr_t freq;
    COPROC_READ_WORD(CNTFRQ, freq);
    return (uint32_t) freq;
}

static inline uint32_t generic_timer_read_ctrl(void)
{
    uintptr_t ctrl;
    COPROC_READ_WORD(CNTP_CTL, ctrl);
    return ctrl;
}

static inline void generic_timer_write_ctrl(uintptr_t ctrl)
{
    COPROC_WRITE_WORD(CNTP_CTL, ctrl);
}

static inline void generic_timer_or_ctrl(uintptr_t bits)
{
    uintptr_t ctrl = generic_timer_read_ctrl();
    generic_timer_write_ctrl(ctrl | bits);
}

static inline void generic_timer_and_ctrl(uintptr_t bits)
{
    uintptr_t ctrl = generic_timer_read_ctrl();
    generic_timer_write_ctrl(ctrl & bits);
}

static inline void generic_timer_enable(void)
{
    generic_timer_or_ctrl(GENERIC_TIMER_ENABLE);
}

static inline void generic_timer_disable(void)
{
    generic_timer_and_ctrl(~GENERIC_TIMER_ENABLE);
}

static inline void generic_timer_unmask_irq(void)
{
    generic_timer_and_ctrl(~GENERIC_TIMER_IMASK);
}

static inline void generic_timer_mask_irq(void)
{
    generic_timer_or_ctrl(GENERIC_TIMER_IMASK);
}

static inline uintptr_t generic_timer_status(void)
{
    return generic_timer_read_ctrl() & GENERIC_TIMER_STATUS;
}

void
init(void)
{
    generic_timer_enable();
    freq_t freq = generic_timer_get_freq();
    uint64_t ticks;
    uint64_t time;
    // printf("freq: %d\n", freq);
    for(int i = 0; true; i++) {
        ticks = generic_timer_get_ticks();
        time = freq_cycles_and_hz_to_ns(ticks, freq);
        
        if (i % 1000000 == 0) {
            printf("time: %d\n", time / 1000000000);
        }
    }
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
