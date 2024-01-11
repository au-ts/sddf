#pragma once

#include <sddf/serial/shared_ringbuffer.h> 

#define BIT(nr) (1UL << (nr))

#define UART_SR1_RRDY          BIT( 9)
#define UART_SR1_TRDY          BIT(13)
/* CR1 */
#define UART_CR1_UARTEN        BIT( 0)
#define UART_CR1_RRDYEN        BIT( 9)
/* CR2 */
#define UART_CR2_SRST          BIT( 0)
#define UART_CR2_RXEN          BIT( 1)
#define UART_CR2_TXEN          BIT( 2)
#define UART_CR2_ATEN          BIT( 3)
#define UART_CR2_RTSEN         BIT( 4)
#define UART_CR2_WS            BIT( 5)
#define UART_CR2_STPB          BIT( 6)
#define UART_CR2_PROE          BIT( 7)
#define UART_CR2_PREN          BIT( 8)
#define UART_CR2_RTEC          BIT( 9)
#define UART_CR2_ESCEN         BIT(11)
#define UART_CR2_CTS           BIT(12)
#define UART_CR2_CTSC          BIT(13)
#define UART_CR2_IRTS          BIT(14)
#define UART_CR2_ESCI          BIT(15)
/* CR3 */
#define UART_CR3_RXDMUXDEL     BIT( 2)
/* FCR */
#define UART_FCR_RFDIV(x)      ((x) * BIT(7))
#define UART_FCR_RFDIV_MASK    UART_FCR_RFDIV(0x7)
#define UART_FCR_RXTL(x)       ((x) * BIT(0))
#define UART_FCR_RXTL_MASK     UART_FCR_RXTL(0x1F)
/* SR2 */
#define UART_SR2_RXFIFO_RDR    BIT(0)
#define UART_SR2_TXFIFO_EMPTY  BIT(14)
/* RXD */
#define UART_URXD_READY_MASK   BIT(15)
#define UART_BYTE_MASK         0xFF
 /* DMA */
#define UCR1_RXDMAEN	(1<<8)	/* Recv ready DMA enable */
#define UCR1_TXDMAEN	(1<<3)	/* Transmitter ready DMA enable */
#define USR1_TRDY	(1<<13) /* Transmitter ready interrupt/dma flag */
#define USR1_RRDY	(1<<9)	 /* Receiver ready interrupt/dma flag */
/* INTERRUPT FLAGS*/
#define USR1_PARITYERR	(1<<15) /* Parity error interrupt flag */
#define IRQ_MASK (USR1_TRDY | USR1_RRDY)

// Might need to copy over the platform specific files, for now copied into one serial.h

#define UART1_PADDR  0x30860000
#define UART2_PADDR  0x30890000
#define UART3_PADDR  0x30880000
#define UART4_PADDR  0x30a60000

#define UART1_IRQ    58
#define UART2_IRQ    59
#define UART3_IRQ    60
#define UART4_IRQ    61

#define UART_REF_CLK 12096000

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

// Move this into a seperate file in the future
#define NUM_BUFFERS 512
#define BUFFER_SIZE 2048

enum serial_parity {
    PARITY_NONE,
    PARITY_EVEN,
    PARITY_ODD
};

struct imx_uart_regs {
    uint32_t rxd;      /* 0x000 Receiver Register */
    uint32_t res0[15];
    uint32_t txd;      /* 0x040 Transmitter Register */
    uint32_t res1[15];
    uint32_t cr1;      /* 0x080 Control Register 1 */
    uint32_t cr2;      /* 0x084 Control Register 2 */
    uint32_t cr3;      /* 0x088 Control Register 3 */
    uint32_t cr4;      /* 0x08C Control Register 4 */
    uint32_t fcr;      /* 0x090 FIFO Control Register */
    uint32_t sr1;      /* 0x094 Status Register 1 */
    uint32_t sr2;      /* 0x098 Status Register 2 */
    uint32_t esc;      /* 0x09c Escape Character Register */
    uint32_t tim;      /* 0x0a0 Escape Timer Register */
    uint32_t bir;      /* 0x0a4 BRM Incremental Register */
    uint32_t bmr;      /* 0x0a8 BRM Modulator Register */
    uint32_t brc;      /* 0x0ac Baud Rate Counter Register */
    uint32_t onems;    /* 0x0b0 One Millisecond Register */
    uint32_t ts;       /* 0x0b4 Test Register */
};
typedef volatile struct imx_uart_regs imx_uart_regs_t;

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