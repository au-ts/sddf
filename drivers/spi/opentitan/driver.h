#include <stdint.h>
#include <stdbool.h>

typedef struct spi_driver_data {
    // Per request state
    spi_cs_line_t cs_line;
    spi_cmd_t *cmd;
    uint16_t num_cmds;
    void *slice_base;
    // Request in-progress state
    uint8_t cmd_in_progress;
    // Command in-progress state (effectively offsets into the slice region)
    uint16_t tx_remaining;
    uint16_t rx_remaining;
    // Error
    spi_err_t err;
} spi_driver_data_t;

typedef enum spi_state {
    IDLE, REQ, SEL_CMD, CMD, CMD_RET, RESP, NUM_STATES
} spi_state_t;

typedef struct fsm_state {
    spi_state_t nxt_state;
    bool yield;
} fsm_state_t;

static void spi_reset_state(spi_driver_data_t *s) {
    s->cs_line = -1;
    s->cmd = NULL;
    s->num_cmds = -1;
    s->slice_base = NULL;
    s->cmd_in_progress = -1;
    s->tx_remaining = -1;
    s->rx_remaining = -1;
    s->err = SPI_ERR_OK;
}

char *fsm_str(spi_state_t state) {
    switch (state) {
        case IDLE:      return "IDLE";
        case REQ:       return "REQ";
        case SEL_CMD:   return "SEL_CMD";
        case CMD:       return "CMD";
        case CMD_RET:   return "CMD_RET";
        case RESP:      return "RESP";
        default:        return "INVALID";
    }
}

#define TIMEOUT_LIMIT (0xFFF)

#define PULP_MAX_CS_LINE        (3)

#define TX_FIFO_WORD_DEPTH      (72)
#define TX_FIFO_BYTE_DEPTH      (TX_FIFO_WORD_DEPTH * sizeof(uint32_t))
#define RX_FIFO_WORD_DEPTH      (64)
#define RX_FIFO_BYTE_DEPTH      (RX_FIFO_WORD_DEPTH * sizeof(uint32_t))
#define MIN_FIFO_WORD_DEPTH     (MIN(TX_FIFO_WORD_DEPTH, RX_FIFO_WORD_DEPTH))
#define MIN_FIFO_BYTE_DEPTH     (MIN_FIFO_WORD_DEPTH * sizeof(uint32_t))


#define DEFAULT_DEVICE_CONFIG   (CONFIGOPTS_CLKDIV(0x7C))

/* Device Macros */
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

#define COMMAND_DIRECTION_TX_ONLY       (BIT(13))
#define COMMAND_DIRECTION_RX_ONLY       (BIT(12))
#define COMMAND_DIRECTION_BIDIRECTION   (BIT(12) | BIT(13))
#define COMMAND_CSAAT                   (BIT(9))

// TODO: Trust me on this, it's stupid
#define COMMAND_LEN_OFFSET(length)      (((length) - 1) & 0x1FF)

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

