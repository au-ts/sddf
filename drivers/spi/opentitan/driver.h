#define CONTROL_SPIEN (BIT(31))
#define CONTROL_SW_RST (BIT(30))
#define CONTROL_OUTPUT_EN (BIT(29))

#define COMMAND_DIRECTION_TX_ONLY (BIT(12))
#define COMMAND_DIRECTION_RX_ONLY (BIT(13))
#define COMMAND_DIRECTION_BIDIRECTION (BIT(12) | BIT(13))

// Trust me on this, it's stupid
#define COMMAND_LEN_OFFSET(length) (((length) - 1) & 0x1FF)

#define STATUS_READY(status)    ((status) & BIT(31))
#define STATUS_ACTIVE(status)   ((status) & BIT(30))
#define STATUS_TXSTALL(status)  ((status) & BIT(27))
#define STATUS_RXQD(status)     (((status) >> 8) & 0xFF)
#define STATUS_TXQD(status)     ((status) & 0xFF)

