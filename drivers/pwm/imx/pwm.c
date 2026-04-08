/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "pwm.h"

#include <os/sddf.h>
#include <stdbool.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/pwm/client.h>
#include <sddf/clk/imx8mq-bindings.h>
#include <sddf/clk/client.h>

// TODO: Clock tree
// TODO: errata ERR051198?

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PWM DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PWM DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define CH_CLOCK_PPC 0
#define CH_CONTROL_PPC 1

#define NUM_PWM_CHANNELS 4

// FIXME: hardcoded in meta.py. clk_rate unknown til runtime
static struct pwm_channel_state {
    volatile imx_pwm_regs_t *regs;
    uint64_t clk_rate;
    uint32_t clk_id;
    uint32_t gate_clk_id;
} pwm_channel_states[NUM_PWM_CHANNELS] = {
    [0] = { .regs = (volatile void *)0x30000000, .clk_id = IMX8MQ_CLK_PWM1, .gate_clk_id = IMX8MQ_CLK_PWM1_ROOT },
    [1] = { .regs = (volatile void *)0x30010000, .clk_id = IMX8MQ_CLK_PWM2, .gate_clk_id = IMX8MQ_CLK_PWM2_ROOT },
    [2] = { .regs = (volatile void *)0x30020000, .clk_id = IMX8MQ_CLK_PWM3, .gate_clk_id = IMX8MQ_CLK_PWM3_ROOT },
    [3] = { .regs = (volatile void *)0x30030000, .clk_id = IMX8MQ_CLK_PWM4, .gate_clk_id = IMX8MQ_CLK_PWM4_ROOT },
};

static inline const uint32_t pwm_mk_control(uint16_t prescalar, uint8_t poutc)
{
    assert(prescalar < BIT(PWMx_PWMCR__PRESCALAR_LEN));
    assert(poutc < BIT(PWMx_PWMCR__POUTC_LEN));

    return ( \
        /* FIFO empty flag is set when there are more than or equal to 1 empty slots in FIFO */
        ((0b00) << PWMx_PWMCR__FWM_SHIFT) |
        /* When this bit is cleared, the input clock is gated off in stop mode. */
        (( 0b0) << PWMx_PWMCR__STOPEN_SHIFT) |
        /* When this bit is cleared, the input clock is gated off in stop mode. */
        (( 0b0) << PWMx_PWMCR__DOZEN_SHIFT) |
        /* When this bit is cleared, the input clock is gated off in stop mode. */
        (( 0b0) << PWMx_PWMCR__WAITEN_SHIFT) |
        /* When this bit is cleared, the input clock is gated off in stop mode. */
        (( 0b0) << PWMx_PWMCR__DBGEN_SHIFT) |
        /* 0 = byte ordering remains the same */
        (( 0b0) << PWMx_PWMCR__BCTR_SHIFT) |
        /* 0 = half word swapping does not take place */
        (( 0b0) << PWMx_PWMCR__HCTR_SHIFT) |
        /* customisable */
        ((poutc) << PWMx_PWMCR__POUTC_SHIFT) |
        /* Use the High-frequency reference clock (ipg_clk_highfreq) */
        ((0b10) << PWMx_PWMCR__CLKSRC_SHIFT) |
        /* customisable */
        ((prescalar) << PWMx_PWMCR__PRESCALAR_SHIFT) |
        /* Use each sample once */
        ((0b00) << PWMx_PWMCR__REPEAT_SHIFT)
    );
}

static void pwm_sw_reset(volatile imx_pwm_regs_t *pwm_regs)
{
    /* disable the PWM by reset. Necessary to clear the 'sample' FIFO. */
    pwm_regs->control = BIT(PWMx_PWMCR__SWR);
    // FIXME: timeout
        /* wait for self-clearing reset bit. should clear after 1 cycle */
    while (pwm_regs->control & BIT(PWMx_PWMCR__SWR));
        /* assert that it is now not enabled */
    assert(!(pwm_regs->control & BIT(PWMx_PWMCR__EN)));

    /* we don't need any interrupts */
    pwm_regs->interrupt = 0;
}

/* [IMX8MDQLQRM] Section 12.2.6 Disable Sequence for the PWM */
static void pwm_disable(volatile imx_pwm_regs_t *pwm_regs)
{
    /* Can be disabled at any time. Any data in FIFO will remain unless
       cleared by a software reset */
    pwm_regs->control &= BIT(PWMx_PWMCR__EN);
}

static void pwm_enable(volatile imx_pwm_regs_t *pwm_regs)
{
    pwm_regs->control |= BIT(PWMx_PWMCR__EN);
}

/* [IMX8MDQLQRM] Section 12.2.4.1 Operation */
static bool pwm_configure(int channel, uint64_t period_ns, uint64_t pulse_width_ns, int flags)
{
    volatile imx_pwm_regs_t *pwm_regs = pwm_channel_states[channel].regs;
    uint64_t clk_rate = pwm_channel_states[channel].clk_rate;

    pwm_disable(pwm_regs);

    /*
        The PWM hardware has a 16-bit up-counter that counts from 0 to the period register,
        and is then reset. The signal starts at 1 (unless you invert the polarity)
        and then when the value in the sample FIFO matches the current count the
        output signal becomes 0. It then continues counting until the period is reached.
     */

    uint8_t poutc;
    if (flags & SDDF_PWM_FLAG_INVERT_POLARITY) {
        poutc = PWMx_PWMCR__POUTC_INVERTED;
    } else {
        poutc = PWMx_PWMCR__POUTC_NORMAL;
    }

    uint64_t clk_period_ns = (1 * 1000UL * 1000UL * 1000UL) / clk_rate;

    // -1 for value to put in prescale
    const uint64_t max_prescale_v = 4096;
    const uint64_t min_prescale_v = 1;

    // -2 for value to put in the period
    const uint64_t max_period_register_v = 0x10000;
    const uint64_t min_period_register_v = 0x2;

    const uint64_t min_period = clk_period_ns * min_prescale_v * min_period_register_v;
    const uint64_t max_period = clk_period_ns * max_prescale_v * max_period_register_v;

    LOG_DRIVER("clock period %ld\n", clk_period_ns);
    LOG_DRIVER("min clock period %ld\n", min_period);
    LOG_DRIVER("max clock period %ld\n", max_period);

    // We're also be lazy here
    if (period_ns < min_period) {
        LOG_DRIVER("requested period too small\n");
        return false;
    } else if (period_ns > max_period) {
        // FIXME: we could update root clock scales in this case
        //        we could potentially do it for min if we can increase the clk freq
        LOG_DRIVER("requested period too large\n");
        return false;
    }

    // TODO: I ignore overflow etc

    uint64_t period_cycles = period_ns / clk_period_ns;
    // add 1 to prevent div-by-zero
    uint64_t prescale_v = period_cycles / max_period_register_v + 1;
    period_cycles /= prescale_v;
    uint64_t pulse_width_cycles = pulse_width_ns / clk_period_ns;
    pulse_width_cycles /= prescale_v;

    LOG_DRIVER("value of prescalar: %ld, period: %ld, sample: %ld\n", prescale_v, period_cycles, pulse_width_cycles);

    assert(period_cycles <= max_period_register_v);
    assert(period_cycles >= min_period_register_v);
    uint16_t period = period_cycles - 2;

    // Done by the error checks earlier this cannot happen.
    assert(prescale_v <= max_prescale_v);
    assert(prescale_v >= min_prescale_v);
    uint16_t prescalar = prescale_v - 1;

    assert(pulse_width_cycles < BIT(16));
    assert(pulse_width_cycles >= 0);
    uint16_t sample = pulse_width_cycles;

    LOG_DRIVER("in registers prescalar: %d, period: %d, sample: %d\n", prescalar, period, sample);

    pwm_regs->control = pwm_mk_control(prescalar, poutc);
    pwm_regs->sample = sample;
    pwm_regs->period = period;

    /* 4. Check/Clear status bits (w1c) to ensure they are all zero */
    if (pwm_regs->status & PWMx_PWMSR__InterruptStatus_MASK) {
        pwm_regs->status = PWMx_PWMSR__InterruptStatus_MASK;
        // This seems to always happen. We don't care about this, though.
        // LOG_DRIVER("PWM status (error) bits are 1: 0x%x\n", pwm_regs->status);
    }

    pwm_enable(pwm_regs);

    return true;
}


void init(void)
{
    LOG_DRIVER("PWM starting\n");

    for (int i = 0; i < NUM_PWM_CHANNELS; i++) {
        int ret;

        ret = sddf_clk_get_rate(CH_CLOCK_PPC, pwm_channel_states[i].clk_id, &pwm_channel_states[i].clk_rate);
        assert(ret == 0);

        LOG_DRIVER("PWM%d clk rate is %ld Hz\n", i, pwm_channel_states[i].clk_rate);

        ret = sddf_clk_enable(CH_CLOCK_PPC, pwm_channel_states[i].gate_clk_id);
        assert(ret == 0);

        pwm_sw_reset(pwm_channel_states[i].regs);

        LOG_DRIVER("PWM%d reset complete\n", i);
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    LOG_DRIVER("ppc from channel %u\n", ch);

    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_PWM_PPC_ID_SET_NS: {
        LOG_DRIVER("set period/pulse width ns request\n");

        // TODO: check msginfo length

        seL4_Word channel = sddf_get_mr(SDDF_PWM_PPC_SLOT_CHANNEL);
        seL4_Word period_ns = sddf_get_mr(SDDF_PWM_PPC_SLOT_PERIOD);
        seL4_Word pulse_width_ns = sddf_get_mr(SDDF_PWM_PPC_SLOT_PULSE_WIDTH);
        seL4_Word flags = sddf_get_mr(SDDF_PWM_PPC_SLOT_FLAGS);

        LOG_DRIVER("... for pwm channel %ld\n", channel);
        LOG_DRIVER("... with period ns %ld\n", period_ns);
        LOG_DRIVER("... with pulse width ns %ld\n", pulse_width_ns);
        LOG_DRIVER("... with flags 0x%lx\n", flags);

        if (channel >= NUM_PWM_CHANNELS) {
            // Invalid channel.
            return microkit_msginfo_new(SDDF_PWM_FAILURE, 0);
        }

        if (period_ns == 0 && pulse_width_ns == 0) {
            pwm_disable(pwm_channel_states[channel].regs);
            return microkit_msginfo_new(SDDF_PWM_SUCCESS, 0);
        } else if (period_ns == 0) {
            // Cannot have 0 period.
            return microkit_msginfo_new(SDDF_PWM_FAILURE, 0);
        } else if (pulse_width_ns >= period_ns) {
            // Cannot have pulse width >= period as this would be duty > 100%
            return microkit_msginfo_new(SDDF_PWM_FAILURE, 0);
        } else {
            bool success = pwm_configure(channel, period_ns, pulse_width_ns, flags);
            return microkit_msginfo_new(success ? SDDF_PWM_SUCCESS : SDDF_PWM_FAILURE, 0);
        }
    }
    default:
        LOG_DRIVER("Unknown request %lu from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        return microkit_msginfo_new(SDDF_PWM_FAILURE, 0);
    }
}

void notified(microkit_channel ch)
{
    LOG_DRIVER_ERR("Unexpected notification on channel %u\n", ch);
}
