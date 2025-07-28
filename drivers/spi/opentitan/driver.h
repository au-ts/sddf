#include <stdint.h>
#include <stdbool.h>

typedef struct spi_driver_data {
    // Per CS state
    void *data_region;
    uint16_t cmd_in_progress;
    spi_cs_t cs;
    // Command
    size_t read_offset;
    size_t write_offset;
    uint16_t len;
    bool cs_active_after_cmd;
    // Command in-progress state
    uint16_t tx_progress;
    uint16_t rx_progress;
    // Error
    spi_err_t err;
} spi_driver_data_t;

typedef enum spi_state {
    SPI_STATE_IDLE, 
    SPI_STATE_CS, 
    SPI_STATE_SEL_CMD, 
    SPI_STATE_CMD, 
    SPI_STATE_CMD_RET, 
    SPI_STATE_RESP, 
} spi_state_t;

typedef struct fsm_state {
    spi_state_t nxt_state;
    bool yield;
} fsm_state_t;

static void spi_reset_state(spi_driver_data_t *s) {
    s->data_region = NULL;
    s->cmd_in_progress = 0;
    s->read_offset = -1;
    s->write_offset = -1;
    s->len = 0;
    s->cs_active_after_cmd = false;
    s->tx_progress = -1;
    s->rx_progress = -1;
    s->err = SPI_ERR_OK;
}

char *fsm_str(spi_state_t state) {
    switch (state) {
        case SPI_STATE_IDLE:      return "IDLE";
        case SPI_STATE_CS:       return "REQ";
        case SPI_STATE_SEL_CMD:   return "SEL_CMD";
        case SPI_STATE_CMD:       return "CMD";
        case SPI_STATE_CMD_RET:   return "CMD_RET";
        case SPI_STATE_RESP:      return "RESP";
        default:        return "INVALID";
    }
}

#define TIMEOUT_LIMIT (0xFFF)

#define PULP_MAX_CS_LINE        (3)

#define FIFO_DEPTH (64)

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

// A small quirk of the hardware, the length reported to the device should be one less than the 
// intended length
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

