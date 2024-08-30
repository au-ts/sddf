/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "usdhc.h"

#include <microkit.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>

#include "blk_config.h"

// #define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("uSDHC DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("uSDHC DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define CHANNEL_CLIENT    0
#define CHANNEL_USDHC_IRQ 1
#define CHANNEL_TIMER     2

#define INT_STATUSES_ENABLED ( \
    USDHC_INT_STATUS_EN_CCSEN   | USDHC_INT_STATUS_EN_TCSEN                                  \
  /* Card Detect through the SDHC registers does not work on iMX8; we use GPIOs instead  */  \
  /* | USDHC_INT_STATUS_EN_CINSSEN | USDHC_INT_STATUS_EN_CRMSEN                           */ \
  | USDHC_INT_STATUS_EN_CTOESEN | USDHC_INT_STATUS_EN_CCESEN   | USDHC_INT_STATUS_EN_CEBESEN \
  | USDHC_INT_STATUS_EN_CIESEN  | USDHC_INT_STATUS_EN_DTOESEN  | USDHC_INT_STATUS_EN_DCSESEN \
  | USDHC_INT_STATUS_EN_DEBESEN | USDHC_INT_STATUS_EN_AC12ESEN | USDHC_INT_STATUS_EN_DMAESEN )
#define INT_SIGNALS_ENABLED ( \
    USDHC_INT_SIGNAL_EN_CCIEN   | USDHC_INT_SIGNAL_EN_TCIEN                                  \
  /* See above comment about Card Detect                                                  */ \
  /* | USDHC_INT_SIGNAL_EN_CINSIEN | USDHC_INT_SIGNAL_EN_CRMIEN                           */ \
  | USDHC_INT_SIGNAL_EN_CTOEIEN | USDHC_INT_SIGNAL_EN_CCEIEN   | USDHC_INT_SIGNAL_EN_CEBEIEN \
  | USDHC_INT_SIGNAL_EN_CIEIEN  | USDHC_INT_SIGNAL_EN_DTOEIEN  | USDHC_INT_SIGNAL_EN_DCSEIEN \
  | USDHC_INT_SIGNAL_EN_DEBEIEN | USDHC_INT_SIGNAL_EN_AC12EIEN | USDHC_INT_SIGNAL_EN_DMAEIEN )

/* See [SD-PHY] 4.3.13 Send Interface Condition; any value is good. */
#define IF_COND_CHECK_PATTERN 0xAA

#define SD_BLOCK_SIZE 512
#define SDDF_BLOCKS_TO_SD_BLOCKS (BLK_TRANSFER_SIZE / SD_BLOCK_SIZE)

#define fallthrough __attribute__((__fallthrough__))

blk_queue_handle_t blk_queue;
volatile imx_usdhc_regs_t *usdhc_regs;
blk_storage_info_t *blk_storage_info;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
uintptr_t blk_data;

/* Make sure to update drv_to_blk_status() as well */
typedef enum {
    DrvSuccess,
    DrvIrqWait,
    DrvErrorInternal,
    DrvErrorCardGone,
    DrvErrorCardIncompatible,
} drv_status_t;

static struct card_info {
    /* Relative Card Address ([SD-PHY] 4.9.5) */
    uint16_t rca;
    /* card capacity status; false = SDSC, true = SDHC/SDXC. TODO(#187): more card types */
    bool ccs;
    /* Current card state */
    sd_card_state_t card_state;
    /* [SD-PHY] 5.3 CSD Register */
    uint32_t csd[4];
} card_info;

#define DRIVER_STATE_INIT 0

typedef enum {
    SendStateInit = DRIVER_STATE_INIT,
    SendStateSend,
    SendStateRecv,
    SendStateDone,
} command_state_t;

static struct driver_state {
    struct command_state {
        command_state_t normal;
        command_state_t app_prefix;
    } command;

    enum {
        ExecutorStateInit = DRIVER_STATE_INIT,
        ExecutorStateActive,
    } executor;

    enum {
        ClientStateIdle = DRIVER_STATE_INIT,
        ClientStateInflight,
    } clients;

    enum {
        CardIdentStateInit = DRIVER_STATE_INIT,
        CardIdentStateIfCond,
        CardIdentStateOpCondInquiry,
        CardIdentStateOpCond,
        CardIdentStateSendCid,
        CardIdentStateSendRca,
        CardIdentStateSendCsd,
        CardIdentStateCardSelect,
        CardIdentStateDone,
    } card_ident;

    uint64_t card_init_start_time;

    enum {
        DataStateInit = DRIVER_STATE_INIT,
        DataStateSend,
    } data_transfer;
} driver_state;

static inline void reset_driver_and_card_state(void)
{
    driver_state = (struct driver_state) {
        .command = {
            .normal = DRIVER_STATE_INIT,
            .app_prefix = DRIVER_STATE_INIT,
        },
        .executor = DRIVER_STATE_INIT,
        .clients = DRIVER_STATE_INIT,
        .card_ident = DRIVER_STATE_INIT,
        .card_init_start_time = DRIVER_STATE_INIT,
        .data_transfer = DRIVER_STATE_INIT,
    };

    card_info = (struct card_info) {
        .rca = 0,
        .ccs = false, /* really: unknown */

        /* [SD-PHY] Section 4.2.1 Card Reset:
        > After power-on by the host, all cards are in Idle State */
        .card_state = CardStateIdle,
        .csd = {0x0, 0x0, 0x0, 0x0},
    };

    // Disable interrupts.
    usdhc_regs->int_status_en = 0x0;
    usdhc_regs->int_signal_en = 0x0;
}

static inline void usdhc_debug(void)
{
    LOG_DRIVER("PRES_STATE: %u, PROT_CTRL: %u, SYS_CTRL: %u, MIX_CTRL: %u\n", usdhc_regs->pres_state, usdhc_regs->prot_ctrl,
               usdhc_regs->sys_ctrl, usdhc_regs->mix_ctrl);
    LOG_DRIVER("CMD_RSP0: %u, CMD_RSP1: %u, CMD_RSP2: %u, CMD_RSP3: %u\n", usdhc_regs->cmd_rsp0, usdhc_regs->cmd_rsp1,
               usdhc_regs->cmd_rsp2, usdhc_regs->cmd_rsp3);
    LOG_DRIVER("INT_STATUS: %u, INT_STATUS_EN: %u, INT_SIGNAL_EN: %u\n", usdhc_regs->int_status, usdhc_regs->int_status_en,
               usdhc_regs->int_signal_en);
    LOG_DRIVER("VEND_SPEC: %u, VEND_SPEC2: %u, BLK_ATT: %u\n", usdhc_regs->vend_spec, usdhc_regs->vend_spec2,
               usdhc_regs->blk_att);
}

static uint32_t get_command_xfr_typ(sd_cmd_t cmd)
{
    // Set bits 29-24 (CMDINDX).
    uint32_t cmd_xfr_typ = ((uint32_t)cmd.cmd_index << USDHC_CMD_XFR_TYP_CMDINX_SHIFT) & USDHC_CMD_XFR_TYP_CMDINX_MASK;

    if (cmd.data_present) {
        cmd_xfr_typ |= USDHC_CMD_XFR_TYP_DPSEL;
    }

    /* [IMX8MDQLQRM] Table 10-42. Relationship between parameters and the name of the response type
     * Note that R7 doesn't exist in the table but is essentially just R1.
     */
    switch (cmd.cmd_response_type) {
    case RespType_None:
        cmd_xfr_typ |= (USDHC_CMD_XFR_TYP_RSPTYP_NONE << USDHC_CMD_XFR_TYP_RSPTYP_SHIFT);
        break;

    case RespType_R2:
        cmd_xfr_typ |= USDHC_CMD_XFR_TYP_CCCEN \
                       | (USDHC_CMD_XFR_TYP_RSPTYP_L136 << USDHC_CMD_XFR_TYP_RSPTYP_SHIFT);
        break;

    case RespType_R3:
    case RespType_R4:
        cmd_xfr_typ |= (USDHC_CMD_XFR_TYP_RSPTYP_L48 << USDHC_CMD_XFR_TYP_RSPTYP_SHIFT);
        break;

    case RespType_R1:
    case RespType_R5:
    case RespType_R6:
    case RespType_R7:
        cmd_xfr_typ |= USHDC_CMD_XFR_TYP_CICEN | USDHC_CMD_XFR_TYP_CCCEN \
                       | (USDHC_CMD_XFR_TYP_RSPTYP_L48 << USDHC_CMD_XFR_TYP_RSPTYP_SHIFT);
        break;

    case RespType_R1b:
        cmd_xfr_typ |= USHDC_CMD_XFR_TYP_CICEN | USDHC_CMD_XFR_TYP_CCCEN \
                       | (USDHC_CMD_XFR_TYP_RSPTYP_L48B << USDHC_CMD_XFR_TYP_RSPTYP_SHIFT);
        break;

    default:
        assert(!"unknown rtype!");
    }

    return cmd_xfr_typ;
}

static blk_resp_status_t drv_to_blk_status(drv_status_t status)
{
    switch (status) {
    case DrvSuccess:
        return BLK_RESP_OK;

    /* TODO: Make this error more specific once we implemented SD error recovery */
    case DrvErrorInternal:
        return BLK_RESP_ERR_UNSPEC;

    case DrvErrorCardGone:
        return BLK_RESP_ERR_NO_DEVICE;

    case DrvErrorCardIncompatible:
    case DrvIrqWait:
    default:
        assert(!"driver bug; should not be possible");
        return 0xff;
    }
}

static bool card_detected(void)
{
#if 0
    /* This doesn't seem to ever work on this SOC; we need to use GPIO for CD */
    return usdhc_regs->pres_state & USDHC_PRES_STATE_CINST;
#endif
    return true;
}

static drv_status_t handle_interrupt_status(sd_cmd_t cmd)
{
    /* Important Note: INT_STATUS register is of the W1C (write 1 to clear) type */
    uint32_t int_status = usdhc_regs->int_status;

    /* !cmd.data_present => !(int_status & USDHC_INT_STATUS_TC) */
    assert(cmd.data_present || !(int_status & USDHC_INT_STATUS_TC));

    /* If any bits aside from Command Complete / Transfer Complete are set... */
    if (int_status & ~(USDHC_INT_STATUS_CC | USDHC_INT_STATUS_TC)) {
        /* [IMX8MDQLQRM] Tables 10-44, 10-45, 10-46.

            TODO: Map the specific errors to something sensible.
            TODO: Run the RST_C / RST_D to reset the comamnd/ data inhibit?
                & Follow the proper [SD-HOST] error handling flow.
         */
        LOG_DRIVER("-> received error response\n");
        usdhc_regs->int_status = 0xffffffff;

        if (!card_detected()) {
            /* If the card isn't detected, the error is because of that */
            return DrvErrorCardGone;
        }

        return DrvErrorInternal;
    }

    if (int_status & USDHC_INT_STATUS_CC) {
        LOG_DRIVER("-> received response\n");
        usdhc_regs->int_status = USDHC_INT_STATUS_CC;
    }

    bool transfer_complete = !!(int_status & USDHC_INT_STATUS_TC);
    if (cmd.data_present && !transfer_complete) {
        /* We want data but the transfer is not yet complete. */
        return DrvIrqWait;
    }

    /*
        [SD-HOST] 2.2.18 Normal Interrupt Status Register states that

            Transfer Complete
                This bit indicates stop of transaction on three cases:
                (1) Completion of data transfer
                (2) Completion of a command pairing with response-with-busy (R1b, R5b)

        [IMX8MDQLQRM] INT_STATUS for TC bit also indicates similarly...

        However, we never get transfer complete interrupts for response-with-busy.
    */

    if (transfer_complete) {
        usdhc_regs->int_status = USDHC_INT_STATUS_TC;
    }

    return DrvSuccess;
}

/**
 * Send a command `cmd` with argument `cmd_arg`.
 *
 * Ref: [IMX8MDQLQRM] 10.3.4.1 Command send & response receive basic operation.
 */
drv_status_t send_command_inner(command_state_t *state, sd_cmd_t cmd, uint32_t cmd_arg)
{
    uint32_t cmd_xfr_typ;
    drv_status_t status;

    switch (*state) {
    case SendStateInit:
        /* [IMX8MDQLQRM] 10.3.7.1.5 Command Transfer Type
           The host driver checks the Command Inhibit DAT field (PRES_STATE[CDIHB]) and
           the \Command Inhibit CMD field (PRES_STATE[CIHB]) in the Present State register
           before writing to this register.
        */
        if (usdhc_regs->pres_state & (USDHC_PRES_STATE_CIHB | USDHC_PRES_STATE_CDIHB)) {
            LOG_DRIVER_ERR("Could not send a command as CMD/DATA-inhibit fields were set\n");
            usdhc_debug();

            return DrvErrorInternal;
        }

        *state = SendStateSend;
        fallthrough;

    case SendStateSend:
        cmd_xfr_typ = get_command_xfr_typ(cmd);

        LOG_DRIVER("Running %s%2u; argument=0x%08x; cmd_xfr_typ=0x%08x; data_present=%s\n",
                   cmd.is_app_cmd ? "ACMD" : " CMD",
                   cmd.cmd_index, cmd_arg, cmd_xfr_typ,
                   cmd.data_present ? "yes" : "no");

        usdhc_regs->cmd_arg = cmd_arg;
        usdhc_regs->cmd_xfr_typ = cmd_xfr_typ;
        *state = SendStateRecv;
        return DrvIrqWait;

    case SendStateRecv:
        status = handle_interrupt_status(cmd);
        if (status != DrvSuccess) {
            return status;
        }

        *state = SendStateDone;
        fallthrough;

    case SendStateDone:
        return DrvSuccess;

    default:
        /* unreachable */
        return DrvIrqWait;
    }
}

drv_status_t send_command(sd_cmd_t cmd, uint32_t cmd_arg)
{
    if (cmd.is_app_cmd && driver_state.command.app_prefix != SendStateDone) {
        /* See description of App-Specific commands in [SD-PHY] 4.3.9 */
        drv_status_t status = send_command_inner(&driver_state.command.app_prefix, SD_CMD55_APP_CMD,
                                                 (uint32_t)card_info.rca << SD_RCA_SHIFT);
        if (status != DrvSuccess) {
            return status;
        }

        /* Check APP_CMD in the card status to ensure was recognised as such */
        uint32_t card_status = usdhc_regs->cmd_rsp0;
        if (!(card_status & SD_CARD_STATUS_APP_CMD)) {
            LOG_DRIVER_ERR("Card does not set APP_CMD status following CMD55\n");
            return DrvErrorCardIncompatible;
        }

        // Sanity check for me.
        assert(driver_state.command.app_prefix == SendStateDone);
    }

    return send_command_inner(&driver_state.command.normal, cmd, cmd_arg);
}

/**
 * Set the clock frequency registers.
 * This ASSUMES that the SD clock has been stopped beforehand, for applicability
 * in the [SD-HOST] 3.2.1 Internal Clock Setup & 3.2.3 Clock Frequency Change
 * sequences.
 *
 * TODO(#187): At the moment, always assumes SDR not dual data rate (DDR), which
 *       affects calculations.
 */
static void set_clock_frequency_registers(sd_clock_freq_t frequency)
{
    /* TODO(#187): We currently don't have a clock driver....
        we inherit a 150MHz clock from U-Boot, so let's use that...
    */
    uint32_t clock_source = 150 * MHZ;
    /* Described by [IMX8MDQLQRM] SYS_CTRL, page 2755.
       Values here are 1-offset compared to datasheet ones */
    uint16_t sdclkfs = 1;
    uint8_t dvs = 1;

    /* This logic is based on code in U-Boot.
        https://github.com/u-boot/u-boot/blob/8937bb265a/drivers/mmc/fsl_esdhc_imx.c#L606-L610
    */
    while ((clock_source / (16 * sdclkfs)) > frequency && sdclkfs < 256) {
        sdclkfs *= 2;
    }

    while (clock_source / (dvs * sdclkfs) > frequency && dvs < 16) {
        dvs++;
    }

    LOG_DRIVER("Found freq %uHz for target %uHz\n", clock_source / (dvs * sdclkfs), frequency);

    /* Remove the offset by 1 */
    sdclkfs >>= 1;
    dvs -= 1;

    uint32_t sys_ctrl = usdhc_regs->sys_ctrl;
    sys_ctrl &= ~(USDHC_SYS_CTRL_DTOCV_MASK | USDHC_SYS_CTRL_SDCLKFS_MASK | USDHC_SYS_CTRL_DVS_MASK);
    sys_ctrl |= (sdclkfs << USDHC_SYS_CTRL_SDCLKFS_SHIFT);
    sys_ctrl |= (dvs << USDHC_SYS_CTRL_DVS_SHIFT);
    sys_ctrl |= ((0b1111) << USDHC_SYS_CTRL_DTOCV_SHIFT); // Set the DTOCV to max

    LOG_DRIVER("Changing clocks(SYS_CTRL) from 0x%x to 0x%x\n", usdhc_regs->sys_ctrl, sys_ctrl);
    usdhc_regs->sys_ctrl = sys_ctrl;
}

static bool has_timed_out(uint64_t start, uint32_t timeout)
{
    return (sddf_timer_time_now(CHANNEL_TIMER) - start) > timeout;
}

/**
 * Waits for the SD clock to stabilise.
 *
 * [IMX8MDQLQRM] Section 10.3.7.1.11 Present State: Field 'SDSTB'
 * > SD clock stable
 * > This status field indicates that the internal card clock is stable.
 * >   0b - Clock is changing frequency and not stable.
 * >   1b - Clock is stable.
 */
void wait_clock_stable()
{
    uint64_t start = sddf_timer_time_now(CHANNEL_TIMER);
    while (!(usdhc_regs->pres_state & USDHC_PRES_STATE_SDSTB)) {
        if (has_timed_out(start, SD_CLOCK_STABLE_TIMEOUT)) {
            LOG_DRIVER_ERR("internal clock never stabilised...\n");
            break;
        }
    }
}

/**
 * [SD-HOST] Section 3.2.3 SD Clock Frequency Change Sequence
 * 1. SD Clock Stop
 * 2. [irrelevant]
 * 3. Change clock parameters
 * 4. [irrelevant]
 * 5. Check internal clock stable; timeout is 150ms.
 */
void usdhc_change_clock_frequency(sd_clock_freq_t frequency)
{
    /* [IMX8MDQLQRM] Section 10.3.6.7 Changing clock frequency
        > To prevent possible glitch on the card clock, clear the FRC_SDCLK_ON
        > bit when changing the clock divisor value (SDCLKFS or DVS in
        > System Control Register) or [...].
        >
        > Also, before changing the clock divisor value, the host driver should
        > make sure that the SDSTB bit is high.
    */
    usdhc_regs->vend_spec &= ~USDHC_VEND_SPEC_FRC_SDCLK_ON;

    wait_clock_stable();
    set_clock_frequency_registers(frequency);
    wait_clock_stable();
}

void usdhc_setup_clock()
{
    // TODO(#187): Set up clocks instead of relying on U-Boot.

    usdhc_change_clock_frequency(ClockSpeedIdentify_400KHz);
}

/*
    Reset the uSDHC (SD Host Controller), bringing all cards back to the idle State.

    Ref: [IMX8MDQLQRM] Section 10.3.4.2.2 Reset
*/
void usdhc_reset(void)
{
    /* [IMX8MDQLQRM] Section 10.3.6.7 Changing clock frequency
        > To prevent possible glitch on the card clock, clear the FRC_SDCLK_ON
        > bit when changing [...] or setting the RSTA bit.
    */
    usdhc_regs->vend_spec &= ~USDHC_VEND_SPEC_FRC_SDCLK_ON;

    /* Software reset for all; wait until it self-clears */
    usdhc_regs->sys_ctrl |= USDHC_SYS_CTRL_RSTA;
    while (usdhc_regs->sys_ctrl & USDHC_SYS_CTRL_RSTA);

    usdhc_setup_clock();

    /* Wait 74 (~80) clock ticks for power up as required by the spec.

       [IMX8MDQLQRM] 10.3.7.1.13 System Control:
        > INITA / Field 27 can only be set when CIHB & CDIHB fields are unset.

       At this stage, there should be no commands happening...
    */
    assert(!(usdhc_regs->pres_state & (USDHC_PRES_STATE_CIHB | USDHC_PRES_STATE_CDIHB)));
    usdhc_regs->sys_ctrl |= USDHC_SYS_CTRL_INITA;
    while (!(usdhc_regs->sys_ctrl & USDHC_SYS_CTRL_INITA));

    /* Set-up registers to desired values */
    usdhc_regs->int_status_en = INT_STATUSES_ENABLED;
    usdhc_regs->int_signal_en = INT_SIGNALS_ENABLED;

    /* Following [1] and [2], we set several registers that are not cleared
       after software reset.

       [1]: https://github.com/BarrelfishOS/barrelfish/blob/master/usr/drivers/imx8x/sdhc/sdhc.c#L166-L175
       [2]: https://github.com/u-boot/u-boot/blob/v2024.07/drivers/mmc/fsl_esdhc_imx.c#L999-L1015
    */
    usdhc_regs->mmc_boot = 0;
    usdhc_regs->clk_tune_ctrl_status = 0;
    usdhc_regs->dll_ctrl = 0;

    /* Enable DMA, Auto-CMD12 */
    usdhc_regs->mix_ctrl = USDHC_MIX_CTRL_DMAEN | USDHC_MIX_CTRL_AC12EN \
                           /* Do multi-block transfers (impl detail: we always do) */
                           | USDHC_MIX_CTRL_MSBSEL | USDHC_MIX_CTRL_BCEN;

    /* Again following [1] and [2] we configure various registers to good values */
    // TODO(#187): UBoot sets these to blocksize/4 on each data command
    // => this is just arbitrarily set to 1 here. What are good values?
    usdhc_regs->wtmk_lvl = (0x01 << 16) | (0x01);
    usdhc_regs->prot_ctrl = (USDHC_PROT_CTRL_DTW_1_BIT << USDHC_PROT_CTRL_DTW_SHIFT)
                            | (USDHC_PROT_CTRL_EMODE_LITTLE << USDHC_PROT_CTRL_EMODE_SHIFT)
                            | (USDHC_PROT_CTRL_DMASEL_SIMPLE << USDHC_PROT_CTRL_DMASEL_SHIFT);

    // TODO(#187): Probably should set up VEND_SPEC as desired...?
}

static void read_r2_response(uint32_t response[4])
{
    /* [IMX8MDQLQRM] Table 10-43 Response bit definition for each response type
        R[127:8] maps to {RSP3[23:0], CMDRSP2, CMDRSP1, CMDRSP0}
    */
    response[0] = (usdhc_regs->cmd_rsp3 << 8) | (usdhc_regs->cmd_rsp2 >> 24);
    response[1] = (usdhc_regs->cmd_rsp2 << 8) | (usdhc_regs->cmd_rsp1 >> 24);
    response[2] = (usdhc_regs->cmd_rsp1 << 8) | (usdhc_regs->cmd_rsp0 >> 24);
    response[3] = (usdhc_regs->cmd_rsp0 << 8);
}

/* [SD-PHY] Section 4.2 Card Identification Mode. Following the flowcharts of
    - Figure 4-1: SD Memory Card State Diagram (card identification mode)
    - Figure 4-2: Card Initialization and Identification Flow (SD Mode)
*/
drv_status_t perform_card_identification_and_select()
{
    drv_status_t status;
    switch (driver_state.card_ident) {
    case CardIdentStateInit:
        /* [SD-PHY] Section 4.21.5 Pre-init mode
            => we now exit this mode and move to idle */
        status = send_command(SD_CMD0_GO_IDLE_STATE, 0x0);
        if (status != DrvSuccess) {
            return status;
        }

        driver_state.command = (struct command_state) {};
        driver_state.card_ident = CardIdentStateIfCond;
        fallthrough;

    case CardIdentStateIfCond:
        /* [SD-PHY] Section 4.3.13 Send Interface Condition Command
            > [19:16] Voltage supplied (VHS) from Table 4-18
            > [15:8 ] Check pattern to any 8-bit pattern.
        */
        status = send_command(SD_CMD8_SEND_IF_COND,
                              (SD_IF_COND_VHS27_36 << SD_IF_COND_VHS_SHIFT) | (IF_COND_CHECK_PATTERN << SD_IF_COND_CHECK_SHIFT));
        if (status == DrvIrqWait) {
            return DrvIrqWait;
        } else if (status == DrvErrorCardGone) {
            LOG_DRIVER("No Card\n");
            return DrvErrorCardGone;
        } else if (status != DrvSuccess) {
            /* TODO: Unhandled card type. */
            LOG_DRIVER_ERR("Ver 1.X SD Card, or Ver2.00 with voltage mismatch not supported\n");
            return DrvErrorCardIncompatible;
        }

        uint32_t r7_resp = usdhc_regs->cmd_rsp0;
        /* [SD-PHY] 4.2.2 Operating Condition Validation
            > If the card can operate on the supplied voltage, the response echoes
            > back the supply voltage and the check pattern that were set in the command argument.
        */
        if (((r7_resp & SD_IF_COND_VHS_MASK) >> SD_IF_COND_VHS_SHIFT) != SD_IF_COND_VHS27_36) {
            LOG_DRIVER_ERR("CMD8: Non-compatible voltage range\n");
            return DrvErrorCardIncompatible;
        } else if (((r7_resp & SD_IF_COND_CHECK_MASK) >> SD_IF_COND_CHECK_SHIFT) != IF_COND_CHECK_PATTERN) {
            LOG_DRIVER_ERR("CMD8: Check pattern is incorrect... got 0x%02lX\n",
                           (r7_resp & SD_IF_COND_CHECK_MASK) >> SD_IF_COND_CHECK_SHIFT);
            return DrvErrorCardIncompatible;
        }

        driver_state.card_ident = CardIdentStateOpCondInquiry;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case CardIdentStateOpCondInquiry:
        /* [SD-PHY] 4.2.3.1 Initialization Command
            > If the voltage window field (bit 23-0) in the argument is set
            > to zero, it is called "inquiry CMD41" that does not start
            > initialization and is use for getting OCR. The inquiry ACMD41
            > shall ignore the other field (bit 31-24) in the argument.
        */
        status = send_command(SD_ACMD41_SD_SEND_OP_COND, 0x0);
        if (status != DrvSuccess) {
            return status;
        }

        uint32_t ocr_register = usdhc_regs->cmd_rsp0;
        // TODO(#187): At the moment, we support and assume 3.3V operation.
        //       => Ideally we should find a compatible set of voltages.
        assert(usdhc_regs->host_ctrl_cap & USDHC_HOST_CTRL_CAP_VS33);
        if (!(ocr_register & (SD_OCR_VDD31_32 | SD_OCR_VDD32_33))) {
            LOG_DRIVER_ERR("Card does not support 3V3 operation");
            return DrvErrorCardIncompatible;
        }

        driver_state.card_ident = CardIdentStateOpCond;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case CardIdentStateOpCond:
        /* [SD-PHY] 4.2.3.1 Initialization Command
           > If the voltage window field (bit 23-0) in the argument is set to
           > non-zero at the first time, it is called "first ACMD41" that starts
           > initialization. The other field (bit 31-24) in the argument is effective.
           >
           > The argument of following ACMD41 shall be the same as that of the first ACMD41.
           >
           > The HCS (Host Capacity Support) bit set to 1 indicates that the
           > host supports SDHC or SDXC Card. The HCS (Host Capacity Support)
           > bit set to 0 indicates that the host supports neither SDHC nor SDXC Card.
           > If HCS is set to 0, SDHC and SDXC Cards never return ready status.
           >
           > The host shall set ACMD41 timeout more than 1 second to abort repeat of
           > issuing ACMD41 when the card does not indicate ready. The timeout count
           > starts from the first ACMD41 which is set voltage window in the argument.
        */
        if (driver_state.card_init_start_time == DRIVER_STATE_INIT) {
            driver_state.card_init_start_time = sddf_timer_time_now(CHANNEL_TIMER);
        }

        do {
            status = send_command(SD_ACMD41_SD_SEND_OP_COND,
                                  SD_OCR_HCS | SD_OCR_VDD31_32 | SD_OCR_VDD32_33);
            if (status != DrvSuccess) {
                return status;
            }
            driver_state.command = (struct command_state) {};

            ocr_register = usdhc_regs->cmd_rsp0;
            if (!(ocr_register & SD_OCR_POWER_UP_STATUS)) {
                LOG_DRIVER("Card not initialised (OCR: 0x%08x), retrying...\n", ocr_register);
            }
        } while (!(ocr_register & SD_OCR_POWER_UP_STATUS)
                 && !has_timed_out(driver_state.card_init_start_time, SD_INITIALISATION_TIMEOUT));

        if (has_timed_out(driver_state.card_init_start_time, SD_INITIALISATION_TIMEOUT)) {
            LOG_DRIVER_ERR("Card initialisation timeout...\n");
            /* If we didn't send SD_OCR_HCS, HCS cards will never initialise
               ... so assume that something similar has happened here */
            return DrvErrorCardIncompatible;
        }

        /* CCS=1, Ver2.00 or later high/extended capciaty            */
        /* CCS=0, Ver2.00 or later Standard Capacity SD Memory Card  */
        card_info.ccs = !!(ocr_register & SD_OCR_CCS);

        card_info.card_state = CardStateReady;
        driver_state.card_ident = CardIdentStateSendCid;
        fallthrough;

    case CardIdentStateSendCid:
        status = send_command(SD_CMD2_ALL_SEND_CID, 0x0);
        if (status != DrvSuccess) {
            return status;
        }

        /* [SD-PHY] The response type R2 describes in 4.9.3.
            We don't do anything with the CID. */

        card_info.card_state = CardStateIdent;
        driver_state.card_ident = CardIdentStateSendRca;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case CardIdentStateSendRca:
        status = send_command(SD_CMD3_SEND_RELATIVE_ADDR, 0x0);
        if (status != DrvSuccess) {
            return status;
        }

        /* [SD-PHY] 4.9.5 R6 (Published RCA response) */
        card_info.rca = (usdhc_regs->cmd_rsp0 & SD_RCA_MASK) >> SD_RCA_SHIFT;

        /* The card is now in the STANDBY state of the 'Data transfer mode' */
        card_info.card_state = CardStateStdby;
        /* [SD-PHY] 4.3 Data Transfer Mode
            > In Data Transfer Mode the host may operate the card in f_PP frequency range.

            TODO(#187): Actually do `usdhc_change_clock_frequency(ClockSpeedDefault_25MHz)`
         */
        driver_state.card_ident = CardIdentStateSendCsd;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case CardIdentStateSendCsd:
        status = send_command(SD_CMD9_SEND_CSD, ((uint32_t)card_info.rca << SD_RCA_SHIFT));
        if (status != DrvSuccess) {
            return status;
        }

        read_r2_response(card_info.csd);

        driver_state.card_ident = CardIdentStateCardSelect;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case CardIdentStateCardSelect:
        status = send_command(SD_CMD7_CARD_SELECT, ((uint32_t)card_info.rca << SD_RCA_SHIFT));
        if (status != DrvSuccess) {
            return status;
        }

        LOG_DRIVER("Card (RCA: 0x%04x) is now waiting in the transfer state\n", card_info.rca);
        card_info.card_state = CardStateTran;

        driver_state.card_ident = CardIdentStateDone;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case CardIdentStateDone:
        return DrvSuccess;

    default:
        /* unreachable */
        return DrvIrqWait;
    }
}

/* [IMX8MDQLQRM] 10.3.4.3.2.1 Normal read

    1. Wait until the card is ready for data
    2. Set the block length with SET_BLOCKLEN
    3. Set the uSDHC block length register
    4. Set the uSDHC number block register
    5. a. Disable the buffer read ready interrupt, configure the DMA settings
       b. enable the uSDHC DMA when sending the command with data transfer
       c. The AC12EN bit should also be set.
    6. Wait for the Transfer Complete interrupt.

    Also reference [SD-PHY] 4.3.3 Data Read.
*/
drv_status_t usdhc_read_blocks(uintptr_t dma_address, uint32_t sector_number, uint16_t sector_count)
{
    drv_status_t status;
    uint32_t data_address;
    switch (driver_state.data_transfer) {
    case DataStateInit:
        // TODO(#187): We shouldn't need to do this for every command I think.
        status = send_command(SD_CMD16_SET_BLOCKLEN, SD_BLOCK_SIZE);
        if (status != DrvSuccess) {
            return status;
        }

        usdhc_regs->blk_att = (usdhc_regs->blk_att & ~USDHC_BLK_ATT_BLKSIZE_MASK) | (SD_BLOCK_SIZE <<
                                                                                     USDHC_BLK_ATT_BLKSIZE_SHIFT);

        usdhc_regs->ds_addr = dma_address;

        /* Select read data transfer direction */
        usdhc_regs->mix_ctrl |= USDHC_MIX_CTRL_DTDSEL;
        usdhc_regs->blk_att &= ~USDHC_BLK_ATT_BLKCNT_MASK;
        usdhc_regs->blk_att |= ((uint32_t)sector_count << USDHC_BLK_ATT_BLKCNT_SHIFT);

        driver_state.data_transfer = DataStateSend;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case DataStateSend:
        /* [SD-PHY] Table 4-24 Block-Oriented Read Commands
            CMD17:
            > Argument: [31:0] data address
            > SDSC Card (CCS=0) uses byte unit address and SDHC and SDXC Cards (CCS=1)
            > use block unit address (512 Bytes unit).
        */
        if (card_info.ccs) {
            data_address = sector_number;
        } else {
            data_address = sector_number * SD_BLOCK_SIZE;
        }
        status = send_command(SD_CMD18_READ_MULTIPLE_BLOCK, data_address);
        if (status != DrvSuccess) {
            return status;
        }

        card_info.card_state = CardStateData;
        driver_state.command = (struct command_state) {};
        card_info.card_state = CardStateTran;
        return DrvSuccess;

    default:
        /* unreachable */
        return DrvIrqWait;
    }
}

/* [IMX8MDQLQRM] 10.3.4.3.1.1 Normal write

    1. Wait until the card is ready for data
    2. Set the block length with SET_BLOCKLEN
    3. Set the uSDHC block length register
    4. Set the uSDHC number block register
    5. a. Disable the buffer write ready interrupt, configure the DMA settings
       b. enable the uSDHC DMA when sending the command with data transfer
       c. The AC12EN bit should also be set.
    6. Wait for the Transfer Complete interrupt.

    Also reference [SD-PHY] 4.3.4 Data Write
*/
drv_status_t usdhc_write_blocks(uintptr_t dma_address, uint32_t sector_number, uint16_t sector_count)
{
    drv_status_t status;
    uint32_t data_address;
    switch (driver_state.data_transfer) {
    case DataStateInit:
        // TODO(#187): We shouldn't need to do this for every command I think.
        status = send_command(SD_CMD16_SET_BLOCKLEN, SD_BLOCK_SIZE);
        if (status != DrvSuccess) {
            return status;
        }

        usdhc_regs->blk_att = (usdhc_regs->blk_att & ~USDHC_BLK_ATT_BLKSIZE_MASK) | (SD_BLOCK_SIZE <<
                                                                                     USDHC_BLK_ATT_BLKSIZE_SHIFT);

        usdhc_regs->ds_addr = dma_address;

        /* Select write data transfer direction */
        usdhc_regs->mix_ctrl &= ~USDHC_MIX_CTRL_DTDSEL;
        usdhc_regs->blk_att &= ~USDHC_BLK_ATT_BLKCNT_MASK;
        usdhc_regs->blk_att |= ((uint32_t)sector_count << USDHC_BLK_ATT_BLKCNT_SHIFT);

        driver_state.data_transfer = DataStateSend;
        driver_state.command = (struct command_state) {};
        fallthrough;

    case DataStateSend:
        /* [SD-PHY] Table 4-25 Block-Oriented Write Commands
            CMD17:
            > Argument: [31:0] data address
            > SDSC Card (CCS=0) uses byte unit address and SDHC and SDXC Cards (CCS=1)
            > use block unit address (512 Bytes unit).
        */
        if (card_info.ccs) {
            data_address = sector_number;
        } else {
            data_address = sector_number * SD_BLOCK_SIZE;
        }
        status = send_command(SD_CMD25_WRITE_MULTIPLE_BLOCK, data_address);
        if (status != DrvSuccess) {
            return status;
        }

        card_info.card_state = CardStateRcv;
        driver_state.command = (struct command_state) {};
        card_info.card_state = CardStateTran;

        return DrvSuccess;

    default:
        /* unreachable */
        return DrvIrqWait;
    }
}

void setup_blk_storage_info()
{
    assert(!blk_storage_info->ready);

    blk_storage_info->sector_size = SD_BLOCK_SIZE;
    // blk_storage_info->read_only = /* TODO(#187): look at write protect flag */
    blk_storage_info->block_size = 1;

    __uint128_t csd = ((__uint128_t)card_info.csd[0] << 96)
                      | ((__uint128_t)card_info.csd[1] << 64)
                      | ((__uint128_t)card_info.csd[2] << 32)
                      | ((__uint128_t)card_info.csd[3] <<  0);

    LOG_DRIVER("CSD Version: %x\n",
               (uint32_t)((csd & SD_CSD_CSD_STRUCTURE_MASK) >> SD_CSD_CSD_STRUCTURE_SHIFT));

    /* [SD-PHY] 5.3.1 CSD Structure specifies the version. */
    switch ((csd & SD_CSD_CSD_STRUCTURE_MASK) >> SD_CSD_CSD_STRUCTURE_SHIFT) {
    case 0b00: {
        /* CSD Version 1 (SDSC); Reference [SD-PHY] 5.3.2
           >
           > The memory capacity of the card is computed from the entries C_SIZE,
           > C_SIZE_MULT and READ_BL_LEN as follows:
           >
           >            memory capacity = BLOCKNR * BLOCK_LEN
           > Where
           >    BLOCKNR = (C_SIZE+1) * MULT
           >    MULT = 2^{C_SIZE_MULT+2}           (C_SIZE_MULT < 8)
           >    BLOCK_LEN = 2^{READ_BL_LEN},       (READ_BL_LEN < 12)
        */
        uint16_t c_size = (csd & SD_CSD_V1_C_SIZE_MASK) >> SD_CSD_V1_C_SIZE_SHIFT;
        uint8_t read_bl_len = (csd & SD_CSD_V1_READ_BL_LEN_MASK) >> SD_CSD_V1_READ_BL_LEN_SHIFT;
        uint8_t c_size_mult = (csd & SD_CSD_V1_C_SIZE_MULT_MASK) >> SD_CSD_V1_C_SIZE_MULT_SHIFT;

        LOG_DRIVER("READ_BL_LEN: %x\n", read_bl_len);
        LOG_DRIVER("C_SIZE: %x\n", c_size);
        LOG_DRIVER("C_SIZE_MULT: %x\n", c_size_mult);

        uint32_t mult = 1 << (c_size_mult + 2);
        uint32_t block_nr = (c_size + 1) * mult;
        uint32_t block_len = 1 << read_bl_len;
        blk_storage_info->capacity = block_nr * block_len / BLK_TRANSFER_SIZE;
        break;
    }

    case 0b01: {
        /* [SD-PHY] 5.3.3 CSD Version 2 (SDHC,SDXC)
           >
           > The user data area capacity is calculated from C_SIZE as follows:
           >
           >             memory capacity = (C_SIZE+1) * 512KByte
        */
        uint32_t c_size = (csd & SD_CSD_V2_C_SIZE_MASK) >> SD_CSD_V2_C_SIZE_SHIFT;
        blk_storage_info->capacity = (c_size + 1) * (512 * 1024) / BLK_TRANSFER_SIZE;
        break;
    }

    case 0b10: {
        /* [SD-PHY] 5.3.4 CSD Version 3 (SDUC)
           >
           > The user data area capacity is calculated from C_SIZE as follows:
           >
           >             memory capacity = (C_SIZE+1) * 512KByte
        */
        uint32_t c_size = (csd & SD_CSD_V3_C_SIZE_MASK) >> SD_CSD_V3_C_SIZE_SHIFT;
        blk_storage_info->capacity = (c_size + 1) * (512 * 1024) / BLK_TRANSFER_SIZE;
        break;
    }

    case 0b11:
        /* Reserved; unsupported. */
        assert(!"todo");
        break;
    }

    LOG_DRIVER("Card size (blocks): %lu\n", blk_storage_info->capacity);

    __atomic_store_n(&blk_storage_info->ready, true, __ATOMIC_RELEASE);
    LOG_DRIVER("Driver initialisation complete\n");
}

void handle_clients(void)
{
    static blk_req_code_t req_code;
    static uintptr_t req_offset;
    static uint32_t req_block_number;
    static uint16_t req_count;
    static uint32_t req_id;
    int err;

    // TODO(#187): Handle overflow with this multiplication...?
    uint32_t block_to_sectors = BLK_TRANSFER_SIZE / SD_BLOCK_SIZE;

    switch (driver_state.clients) {
    case ClientStateIdle:
        err = blk_dequeue_req(&blk_queue, &req_code, &req_offset, &req_block_number, &req_count, &req_id);
        if (err == -1) {
            // no requests to handle
            return;
        }

        LOG_DRIVER("Received command: code=%d, offset=0x%lx, block_number=%d, count=%d, id=%d\n",
                   req_code, req_offset, req_block_number, req_count, req_id);

        driver_state.clients = ClientStateInflight;
        fallthrough;

    case ClientStateInflight: {
        uint16_t success_count = 0;
        drv_status_t status;

        switch (req_code) {
        case BLK_REQ_READ:
            status = usdhc_read_blocks(req_offset, req_block_number * block_to_sectors,
                                       req_count * block_to_sectors);
            if (status == DrvIrqWait) {
                return;
            }
            driver_state.data_transfer = DataStateInit;

            success_count = 1;
            break;

        case BLK_REQ_WRITE:
            status = usdhc_write_blocks(req_offset, req_block_number * block_to_sectors,
                                        req_count * block_to_sectors);
            if (status == DrvIrqWait) {
                return;
            }
            driver_state.data_transfer = DataStateInit;

            success_count = 1;
            break;

        case BLK_REQ_FLUSH:
        case BLK_REQ_BARRIER:
            /* No-ops. */
            status = DrvSuccess;
            success_count = req_count;
            break;

        default:
            LOG_DRIVER_ERR("Unknown command code: %d\n", req_code);
            return;
        }

        int err = blk_enqueue_resp(&blk_queue, drv_to_blk_status(status), success_count, req_id);
        assert(!err);
        LOG_DRIVER("Enqueued response: status=%d, success_count=%d, id=%d\n", drv_to_blk_status(status), success_count, req_id);
        microkit_notify(CHANNEL_CLIENT);

        driver_state.clients = ClientStateIdle;
        return handle_clients();
    }

    default:
        assert(!"unreachable");
    }
}

void usdhc_executor(bool is_irq)
{
    if (driver_state.executor == ExecutorStateInit && !is_irq) {
        /* Ignore client requests until we're ready (at which point we will process them) */
        return;
    }

    drv_status_t status;
    switch (driver_state.executor) {
    case ExecutorStateInit:
        status = perform_card_identification_and_select();
        if (status != DrvSuccess) {
            return;
        }
        setup_blk_storage_info();

        driver_state.executor = ExecutorStateActive;
        fallthrough;

    case ExecutorStateActive:
        handle_clients();
        // We always stay in the Active state now.
        break;

    default:
        assert(!"unreachable");
    }
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case CHANNEL_USDHC_IRQ:
        usdhc_executor(true);
        break;

    case CHANNEL_CLIENT:
        usdhc_executor(false);
        break;

    case CHANNEL_TIMER:
        LOG_DRIVER("got timer interrupt -- UNHANDLED\n");
        assert(false);
        break;

    default:
        LOG_DRIVER_ERR("notification on unknown channel: %d\n", ch);
        break;
    }

    if (ch == CHANNEL_USDHC_IRQ) {
        microkit_irq_ack(ch);
    }
}

void init()
{
    reset_driver_and_card_state();

    LOG_DRIVER("Beginning driver initialisation...\n");

    /* Setup the sDDF block queue */
    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, BLK_QUEUE_CAPACITY_DRIV);

    /* Make sure we have DMA support. */
    assert(usdhc_regs->host_ctrl_cap & USDHC_HOST_CTRL_CAP_DMAS);

    usdhc_reset();
    usdhc_executor(true);
}
