/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>

/*
    The driver is based on:

    [IMX8MDQLQRM]: i.MX8 Quad i.MX 8M Dual/8M QuadLite/8M Quad Applications Processors Reference Manual
                   Document Number: IMX8MDQLQRM, Rev 3.1, 06/2021.
                   https://www.nxp.com/webapp/Download?colCode=IMX8MDQLQRM
*/

/* [IMX8MDQLQRM] Section 12.2.7 PWM Memory Map/Register Definition

   There are 4 instances of this PWM peripheral.
*/
typedef struct imx_pwm_regs {
    uint32_t control;    /* Control Register   (PWMCR)    (RW)   */
    uint32_t status;     /* Status Register    (PWMSR)    (w1c)  */
    uint32_t interrupt;  /* Interrupt Register (PWMIR)    (RW)   */
    uint32_t sample;     /* Sample Register    (PWMSAR)   (RW)   */
    uint32_t period;     /* Period Register    (PWMSPR)   (RW)   */
    uint32_t counter;    /* Counter Register   (PWMSCNR)  (RO)   */
} imx_pwm_regs_t;

#define _LEN(start, end) ((end - start) + 1)
#define _MASK(start, end)  ((BIT(_LEN(start, end)) - 1) << (start))

/* [IMX8MDQLQRM] Section 12.2.7.1 PWM Control Register  */
#define PWMx_PWMCR__FWM_SHIFT        26       /* FIFO Water Mark */
#define PWMx_PWMCR__STOPEN_SHIFT     25       /* Stop Mode Enable */
#define PWMx_PWMCR__DOZEN_SHIFT      24       /* Doze Mode Enable */
#define PWMx_PWMCR__WAITEN_SHIFT     23       /* Wait Mode Enable */
#define PWMx_PWMCR__DBGEN_SHIFT      22       /* Debug Mode Enable */
#define PWMx_PWMCR__BCTR_SHIFT       21       /* Byte Data Swap Control */
#define PWMx_PWMCR__HCTR_SHIFT       20       /* Half-Word Data Swap Control */
#define PWMx_PWMCR__CLKSRC_SHIFT     16       /* Select Clock Source */
#define PWMx_PWMCR__SWR               3       /* Software Reset */
#define PWMx_PWMCR__REPEAT_SHIFT      1       /* Sample Repeat */
#define PWMx_PWMCR__EN                0       /* Enable */

#define PWMx_PWMCR__PRESCALAR_SHIFT   4             /* Counter Clock Prescalar Value (12 bits) */
#define PWMx_PWMCR__PRESCALAR_LEN     12             /* Counter Clock Prescalar Value (12 bits) */
#define PWMx_PWMCR__PRESCALAR_MASK   _MASK(4, 15)   /* Counter Clock Prescalar Value (12 bits) */

#define PWMx_PWMCR__POUTC_SHIFT      18             /* PWM Output Configuration */
#define PWMx_PWMCR__POUTC_LEN        2              /* PWM Output Configuration */
#define PWMx_PWMCR__POUTC_MASK       _MASK(18, 19)  /* PWM Output Configuration */
#define PWMx_PWMCR__POUTC_NORMAL     0b00
#define PWMx_PWMCR__POUTC_INVERTED   0b01

/* [IMX8MDQLQRM] Section 12.2.7.3 PWM Status Register  */
#define PWMx_PWMSR__FWE               6       /* FIFO Write Error Status */
#define PWMx_PWMSR__CMP               5       /* Compare Status */
#define PWMx_PWMSR__ROV               4       /* Roll-over Status */
#define PWMx_PWMSR__FE                3       /* FIFO Empty Status */

#define PWMx_PWMSR__InterruptStatus_MASK (        \
    BIT(PWMx_PWMSR__FWE) | BIT(PWMx_PWMSR__CMP) | \
    BIT(PWMx_PWMSR__ROV) | BIT(PWMx_PWMSR__FE)    \
)

/* [IMX8MDQLQRM] Section 12.2.7.3 PWM Interrupt Register  */
#define PWMx_PWMIR__CIE               2       /* Compare Interrupt Enable */
#define PWMx_PWMIR__RIE               1       /* Roll-over Interrupt Enable */
#define PWMx_PWMIR__FIE               0       /* FIFO Empty Interrupt Enable */
