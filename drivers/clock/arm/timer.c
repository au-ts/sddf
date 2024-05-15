#include <microkit.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#if !(CONFIG_EXPORT_PCNT_USER && CONFIG_EXPORT_PTMR_USER)
#error "ARM generic timer is not exported by seL4"
#endif

static uint64_t timer_freq;

#define IRQ_CH 0
#define MAX_TIMEOUTS 6

#define GENERIC_TIMER_ENABLE (1 << 0)
#define GENERIC_TIMER_IMASK  (1 << 1)
#define GENERIC_TIMER_STATUS (1 << 2)

#define COPROC_WRITE_WORD(R,W) asm volatile ("msr " R  ", %0" :: "r"(W))
#define COPROC_READ_WORD(R,W)  asm volatile ("mrs %0, " R : "=r" (W))
#define COPROC_WRITE_64(R,W)   COPROC_WRITE_WORD(R,W)
#define COPROC_READ_64(R,W)    COPROC_READ_WORD(R,W)

/* control reigster for the el1 physical timer */
#define CNTP_CTL "cntp_ctl_el0"
/* holds the compare value for the el1 physical timer */
#define CNTP_CVAL "cntp_cval_el0"
/* holds the 64-bit physical count value */
#define CNTPCT "cntpct_el0"
/* frequency of the timer */
#define CNTFRQ "cntfrq_el0"

static inline uint64_t get_ticks(void)
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

static inline void generic_timer_enable(void)
{
    generic_timer_or_ctrl(GENERIC_TIMER_ENABLE);
}

#define KHZ (1000)
#define MHZ (1000 * KHZ)
#define GHZ (1000 * MHZ)

static inline uint64_t freq_cycles_and_hz_to_ns(uint64_t ncycles, uint64_t hz)
{
    if (hz % GHZ == 0) {
        return ncycles / (hz / GHZ);
    } else if (hz % MHZ == 0) {
        return ncycles * MS_IN_S / (hz / MHZ);
    } else if (hz % KHZ == 0) {
        return ncycles * US_IN_S / (hz / KHZ);
    }

    return (ncycles * NS_IN_S) / hz;
}

static inline uint64_t freq_ns_and_hz_to_cycles(uint64_t ns, uint64_t hz)
{
    return (ns * hz) / NS_IN_S;
}

void set_timeout(uint64_t timeout)
{
    generic_timer_set_compare(freq_ns_and_hz_to_cycles(timeout, timer_freq));
}

static uint64_t timeouts[MAX_TIMEOUTS];
static microkit_channel active_channel = -1;
static bool timeout_active = false;
static uint64_t current_timeout;
static uint8_t pending_timeouts;

static void handle_irq(microkit_channel ch)
{
    if (timeout_active) {
        generic_timer_set_compare(UINT64_MAX);
        timeout_active = false;
        microkit_channel curr_channel = active_channel;
        timeouts[curr_channel] = 0;
        // notify the client.
        microkit_notify(curr_channel);
    }

    if (pending_timeouts && !timeout_active) {
        uint64_t curr_time = get_ticks();
        /* find next timeout */
        uint64_t next_timeout = UINT64_MAX;
        microkit_channel ch = -1;

        /* A more efficient solution would be to order these in terms of
         * timeout time, so then we can just take the head as the next timeout.
         * However, this would require a different data structure...
         */
        for (unsigned i = 0; i < MAX_TIMEOUTS; i++) {
            /* Check if any of these timeouts have gone off in the interim */
            if (timeouts[i] != 0 && timeouts[i] <= curr_time) {
                timeouts[i] = 0;
                pending_timeouts--;
                microkit_notify(i);
            } else if (timeouts[i] != 0 && timeouts[i] < next_timeout) {
                next_timeout = timeouts[i];
                ch = i;
            }
        }

        if (ch != -1) {
            pending_timeouts--;
            set_timeout(next_timeout);
            timeout_active = true;
            current_timeout = next_timeout;
            active_channel = ch;
        }
    }
}

void init()
{
    generic_timer_set_compare(UINT64_MAX);
    generic_timer_enable();
    timer_freq = generic_timer_get_freq();
}

void notified(microkit_channel ch)
{
    assert(ch == IRQ_CH);

    handle_irq(ch);
    microkit_irq_ack_delayed(ch);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    uint64_t rel_timeout, cur_ticks, abs_timeout;
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME:
        // Just wants the time. Return it in nanoseconds.
        cur_ticks = get_ticks();
        seL4_SetMR(0, freq_cycles_and_hz_to_ns(cur_ticks, timer_freq));
        return microkit_msginfo_new(0, 1);
    case SDDF_TIMER_SET_TIMEOUT:
        /* The timer talks cycles, but our API is in nanoseconds.
         * Our goal is to set the absolute timeout, which will be
         * in nanoseconds.
         * This means we need to convert current ticks to nanoseconds
         * and add that to what we get from the client.
         */
        // Request to set a timeout.
        rel_timeout = (uint64_t)(seL4_GetMR(0));
        cur_ticks = freq_cycles_and_hz_to_ns(get_ticks(), timer_freq);
        abs_timeout = cur_ticks + rel_timeout;

        timeouts[ch] = abs_timeout; // in nanoseconds
        if (!timeout_active || abs_timeout < current_timeout) {
            if (timeout_active) {
                /* there current timeout is now treated as pending */
                pending_timeouts++;
            }
            // sddf_dprintf("setting timeout to %lu, rel_timeout is %lu\n", abs_timeout, rel_timeout);
            set_timeout(abs_timeout);
            timeout_active = true;

            /* We need to keep track of how far into the future this is so
                we can order client requests appropriately. */
            current_timeout = abs_timeout;
            active_channel = ch;
        } else {
            pending_timeouts++;
        }
        break;
    default:
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n", microkit_msginfo_get_label(msginfo),
                     ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}
