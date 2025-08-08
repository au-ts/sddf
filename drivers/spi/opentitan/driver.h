/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <sddf/spi/queue.h>

/* This driver is based on:

    PULP patches to OpenTitan peripherals
    https://github.com/pulp-platform/opentitan_peripherals/blob/master/sw/include/spi_host_regs.h
    Commit ID: cd3153de2783abd3d03d0595e6c4b32413c62f14

 */

/* Memory map of the registers */
struct spi_regs {
    uint32_t INTR_STATE;
    uint32_t INTR_ENABLE;
    uint32_t INTR_TEST;
    uint32_t ALERT_TEST;
    uint32_t CONTROL;
    uint32_t STATUS;
    uint32_t CONFIGOPTS0;
    uint32_t CONFIGOPTS1;
    uint32_t CONFIGOPTS2;
    uint32_t CSID;
    uint32_t COMMAND;
    uint32_t RXDATA;
    uint32_t TXDATA;
    uint32_t ERROR_ENABLE;
    uint32_t ERROR_STATUS;
    uint32_t EVENT_ENABLE;
};

/* Data required for the driver as it advances through the FSM */
typedef struct spi_driver_data {
    // Per CS state
    spi_cs_t cs;
    void *data_region;
    uint16_t cmd_in_progress;
    // Logical command
    size_t read_offset;
    size_t write_offset;
    uint32_t len; // Needs to be a u32, since the u16 is interpretted as [1, 65536]
    bool cs_active_after_cmd;
    // Logical command in-progress state
    uint32_t logical_progress;
    // Physical command in-progress state
    uint32_t phy_cmd_len;
    uint32_t tx_progress;
    uint32_t rx_progress;
    // Error
    spi_status_t err;
} spi_driver_data_t;

static void spi_reset_state(spi_driver_data_t *s)
{
    s->cs = -1;
    s->data_region = NULL;
    s->cmd_in_progress = 0;
    s->read_offset = -1;
    s->write_offset = -1;
    s->len = 0;
    s->cs_active_after_cmd = false;
    s->logical_progress = -1;
    s->phy_cmd_len = 0;
    s->tx_progress = -1;
    s->rx_progress = -1;
    s->err = SPI_STATUS_OK;
}

typedef enum spi_state {
    SPI_STATE_IDLE,
    SPI_STATE_GET_CS,
    SPI_STATE_GET_LOGICAL_CMD,
    SPI_STATE_ISSUE_PHY_CMD,
    SPI_STATE_EXEC_PHY_CMD,
    SPI_STATE_AWAIT_PHY_CMD,
    SPI_STATE_RESP,
} spi_state_t;

typedef struct fsm_state {
    spi_state_t nxt_state;
    bool yield;
} fsm_state_t;

char *fsm_str(spi_state_t state)
{
    switch (state) {
    case SPI_STATE_IDLE:
        return "IDLE";
    case SPI_STATE_GET_CS:
        return "GET_CS";
    case SPI_STATE_GET_LOGICAL_CMD:
        return "GET_LOGICAL_CMD";
    case SPI_STATE_ISSUE_PHY_CMD:
        return "ISSUE_PHY_CMD";
    case SPI_STATE_EXEC_PHY_CMD:
        return "EXEC_PHY_CMD";
    case SPI_STATE_AWAIT_PHY_CMD:
        return "AWAIT_PHY_CMD";
    case SPI_STATE_RESP:
        return "RESP";
    default:
        return "INVALID";
    }
}

#define TIMEOUT_LIMIT (0xFFF)

#define PULP_MAX_CS_LINE        (3)
#define FIFO_DEPTH      (64)
#define ERROR_IRQ       (0)
#define EVENT_IRQ       (1)

/* Register Macros */
#define INTR_ERROR      (BIT(0))
#define INTR_SPI_EVENT  (BIT(1))

#define CONTROL_SPIEN                   (BIT(31))
#define CONTROL_SW_RST                  (BIT(30))
#define CONTROL_OUTPUT_EN               (BIT(29))
#define CONTROL_TX_WATERMARK(num)       (((num) & 0xFF) << 8)
#define CONTROL_RX_WATERMARK_MASK       (0xFF)
#define CONTROL_RX_WATERMARK(num)       ((num) & CONTROL_RX_WATERMARK_MASK)

#define CONFIGOPTS_CLKDIV(div)          ((div) & 0xFFFF)
#define CONFIGOPTS_CSNIDLE(num)         (((num) & 0xF) << 16)
#define CONFIGOPTS_CSNTRAIL(num)        (((num) & 0xF) << 20)
#define CONFIGOPTS_CSNLEAD(num)         (((num) & 0xF) << 24)
#define CONFIGOPTS_FULLCYC              (BIT(29))
#define CONFIGOPTS_CPHA                 (BIT(30))
#define CONFIGOPTS_CPOL                 (BIT(31))

typedef enum command_direction {
    COMMAND_DIRECTION_TX_ONLY = BIT(13),
    COMMAND_DIRECTION_RX_ONLY = BIT(12),
    COMMAND_DIRECTION_BIDIRECTION = BIT(12) | BIT(13),
    COMMAND_DIRECTION_DUMMY_CYCLES = 0,
} command_direction_t;

#define COMMAND_CSAAT                   (BIT(9))

// A small quirk of the hardware, the length reported to the device should be one less than the
// intended length
#define COMMAND_LEN_MAX                 (0x1FF + 0x1)
#define COMMAND_LEN(length)      (((length) - 1) & (COMMAND_LEN_MAX - 1))

#define STATUS_READY(status)    ((status) & BIT(31))
#define STATUS_ACTIVE(status)   ((status) & BIT(30))
#define STATUS_TXEMPTY(status)  ((status) & BIT(28))
#define STATUS_TXSTALL(status)  ((status) & BIT(27))
#define STATUS_RXWM(status)     ((status) & BIT(20))
#define STATUS_RXQD(status)     (((status) & 0xFF00) >> 8)
#define STATUS_TXQD(status)     ((status) & 0xFF)

/* Access invalid is always active */
#define ERROR_ACCESSINVAL       (BIT(5))
#define ERROR_CSIDINVAL         (BIT(4))
#define ERROR_CMDINVAL          (BIT(3))
#define ERROR_UNDERFLOW         (BIT(2))
#define ERROR_OVERFLOW          (BIT(1))
#define ERROR_CMDBUSY           (BIT(0))

#define ERROR_MASK              (ERROR_ACCESSINVAL | ERROR_CSIDINVAL | \
                                ERROR_CMDINVAL | ERROR_UNDERFLOW | \
                                ERROR_OVERFLOW | ERROR_CMDBUSY)

#define EVENT_ENABLE_IDLE       (BIT(5))
#define EVENT_ENABLE_READY      (BIT(4))
#define EVENT_ENABLE_TXWM       (BIT(3))
#define EVENT_ENABLE_RXWM       (BIT(2))
#define EVENT_ENABLE_TXEMPTY    (BIT(1))
#define EVENT_ENABLE_RXFULL     (BIT(0))
