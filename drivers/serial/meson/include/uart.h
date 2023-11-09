#pragma once

#include "shared_ringbuffer.h"

#define BIT(nr) (1UL << (nr))

/* The driver is based on the Amlogic S905X3 Data Sheet Revision 02.

The following register descriptions and layout are from section 13.5.4.*/

struct meson_uart_regs {
    uint32_t wfifo;      /* 0x000 Write Data */
    uint32_t rfifo;      /* 0x040 Read Data */
    uint32_t cr;         /* 0x080 Control Register */
    uint32_t sr;         /* 0x0c0 Status Register */
    uint32_t irqc;       /* 0x100 IRQ Control Register*/
    uint32_t reg5;       /* 0x140 Baud Rate Control */
};
typedef volatile struct meson_uart_regs meson_uart_regs_t;

/*
Serial driver global state
*/
struct serial_driver {
    int echo;
    int mode;

    /* Values for handling line mode */
    uintptr_t line_buffer;
    int line_buffer_size;
};

/* LINE CONFIG */
#define RAW_MODE 0
#define LINE_MODE 1
#define ECHO_DIS 0
#define ECHO_EN 1

/* LINE CONTROL */
#define ETX 3   /* ctrl+c */
#define EOT 4   /* ctrl+d */
#define BS 8    /* backspace */
#define LF 10   /* Line feed/new line */
#define CR 13   /* Carriage return */
#define NEG 21  /* ctrl+u */
#define SB 26   /* ctrl+z*/
#define SP 32   /* Space*/
#define DL 127  /* Delete */

/* AML_UART_CONTROL bits */
#define AML_UART_TX_EN			BIT(12)
#define AML_UART_RX_EN			BIT(13)
#define AML_UART_TWO_WIRE_EN		BIT(15)
#define AML_UART_STOP_BIT_LEN_MASK	(0x03 << 16)
#define AML_UART_STOP_BIT_1SB		(0x00 << 16)
#define AML_UART_STOP_BIT_2SB		(0x01 << 16)
#define AML_UART_PARITY_TYPE		BIT(18)
#define AML_UART_PARITY_EN		BIT(19)
#define AML_UART_TX_RST			BIT(22)
#define AML_UART_RX_RST			BIT(23)
#define AML_UART_CLEAR_ERR		BIT(24)
#define AML_UART_RX_INT_EN		BIT(27)
#define AML_UART_TX_INT_EN		BIT(28)
#define AML_UART_DATA_LEN_MASK		(0x03 << 20)
#define AML_UART_DATA_LEN_8BIT		(0x00 << 20)
#define AML_UART_DATA_LEN_7BIT		(0x01 << 20)
#define AML_UART_DATA_LEN_6BIT		(0x02 << 20)
#define AML_UART_DATA_LEN_5BIT		(0x03 << 20)
/* AML_UART_STATUS bits */
#define AML_UART_PARITY_ERR		BIT(16)
#define AML_UART_FRAME_ERR		BIT(17)
#define AML_UART_TX_FIFO_WERR		BIT(18)
#define AML_UART_RX_EMPTY		BIT(20)
#define AML_UART_TX_FULL		BIT(21)
#define AML_UART_TX_EMPTY		BIT(22)
#define AML_UART_XMIT_BUSY		BIT(25)
#define AML_UART_ERR			(AML_UART_PARITY_ERR | AML_UART_FRAME_ERR  | AML_UART_TX_FIFO_WERR)
/* AML_UART_IRQ bits */
#define AML_UART_XMIT_IRQ(c)		(((c) & 0xff) << 8)
#define AML_UART_RECV_IRQ(c)		((c) & 0xff)
/* AML_UART_REG5 bits */
#define AML_UART_BAUD_MASK		0x7fffff
#define AML_UART_BAUD_USE		BIT(23)
#define AML_UART_BAUD_XTAL		BIT(24)
#define AML_UART_BAUD_XTAL_DIV2		BIT(27)

// TODO - Fix ref clk 
#define UART_REF_CLK 16660000

#define DIV_ROUND_CLOSEST(x, divisor)(			\
{							\
	typeof(x) __x = x;				\
	typeof(divisor) __d = divisor;			\
	(((typeof(x))-1) > 0 ||				\
	 ((typeof(divisor))-1) > 0 ||			\
	 (((__x) > 0) == ((__d) > 0))) ?		\
		(((__x) + ((__d) / 2)) / (__d)) :	\
		(((__x) - ((__d) / 2)) / (__d));	\
}							\
)

enum serial_parity {
    PARITY_NONE,
    PARITY_EVEN,
    PARITY_ODD
};

