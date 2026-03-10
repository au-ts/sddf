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

// TODO: Clock tree
// TODO: Pinmux
// TODO: support for more than one PWM output per client
// TODO: errata ERR051198

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PWM DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PWM DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)


#define CH_PWM_IRQ 0
#define CH_CONTROL_PPC 1

// FIXME: hardcoded in meta.py
static volatile imx_pwm_regs_t *pwm_regs = (volatile void *)0x30000000;

static inline uint32_t pwm_mk_control(uint16_t prescalar, uint8_t poutc)
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

static void pwm_sw_reset(void)
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
static void pwm_disable(void)
{
    /* Can be disabled at any time. Any data in FIFO will remain unless
       cleared by a software reset */
    pwm_regs->control &= BIT(PWMx_PWMCR__EN);
}

static void pwm_enable(void)
{
    pwm_regs->control |= BIT(PWMx_PWMCR__EN);
}

/* [IMX8MDQLQRM] Section 12.2.4.1 Operation */
static bool pwm_configure(uint64_t period_ns, uint64_t pulse_width_ns, int flags)
{
    pwm_disable();

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

#if 0
    /* The peripheral clock ticks up at a certain rate */
    // FIXME hacks?
    uint64_t clk_rate = 83333333;

    uint64_t min_ns = clk_rate / /* prescale */ 4096 *  1 /* count */;
    uint64_t max_ns = clk_rate / /* prescale */ 1 *  0xFFFE /* count */;
#endif

    uint16_t prescalar = 0;
    uint16_t period = 0x4000;
    uint16_t sample = 0x1000;

    // Writing 0xFFFF to this register will achieve the same result as writing 0xFFFE.
    if (period == 0xFFFF) {
        LOG_DRIVER_ERR("period would be out of range\n");
        return false;
    }

    // Note: PWMO (Hz) = PCLK(Hz) / (period +2).

    // TODO: Settings PWM_PWMPR to 0xFFFF when PWMx_PWMCR REPEAT bits are set to non-zero values is not allowed.

    pwm_regs->control = pwm_mk_control(prescalar, poutc);
    pwm_regs->sample = sample;
    pwm_regs->period = period;

    /* 4. Check/Clear status bits (w1c) to ensure they are all zero */
    if (pwm_regs->status & PWMx_PWMSR__InterruptStatus_MASK) {
        LOG_DRIVER_ERR("PWM status (error) bits are 1: 0x%x\n", pwm_regs->status);
    }
    pwm_regs->status = PWMx_PWMSR__InterruptStatus_MASK;

    pwm_enable();

    return true;
}


void init(void)
{
    LOG_DRIVER("PWM starting\n");

    pwm_sw_reset();
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    LOG_DRIVER("ppc from channel %u\n", ch);

    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_PWM_PPC_ID_SET_NS: {
        LOG_DRIVER("PPC set NS request\n");

        seL4_Word channel = sddf_get_mr(SDDF_PWM_PPC_SLOT_CHANNEL);
        // TODO: channel unsupported.
        assert(channel == 0);

        seL4_Word period_ns = sddf_get_mr(SDDF_PWM_PPC_SLOT_PERIOD);
        seL4_Word pulse_width_ns = sddf_get_mr(SDDF_PWM_PPC_SLOT_PULSE_WIDTH);
        seL4_Word flags = sddf_get_mr(SDDF_PWM_PPC_SLOT_FLAGS);

        if (period_ns == 0 && pulse_width_ns == 0) {
            pwm_disable();
            return microkit_msginfo_new(SDDF_PWM_SUCCESS, 0);
        } else {
            bool success = pwm_configure(period_ns, pulse_width_ns, flags);
            return microkit_msginfo_new(success ? SDDF_PWM_SUCCESS : SDDF_PWM_FAILURE, 0);
        }
    }
    default:
        LOG_DRIVER("Unknown request %lu from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        // XXXX.
        return microkit_msginfo_new(0, 0);
    }
}

void notified(microkit_channel ch)
{
    LOG_DRIVER_ERR("Unexpected notification on channel %u\n", ch);
}
