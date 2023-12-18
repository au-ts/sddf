#pragma once

#include <sddf/serial/shared_ringbuffer.h> 

/*
 * This UART driver is based on the following specificion:
 * ARM PrimeCell UART (PL011)
 * Revision: r1p5
 */

/* Register layout is based on section 3.2 of the specification. */
struct pl011_uart_regs {
    uint32_t dr;        /* 0x000 Data Register */
    uint32_t rsr_ecr;   /* 0x004 Receive Status Register/Error Clear Register */
    uint32_t res1;      /* 0x008 Reserved */
    uint32_t res2;      /* 0x00c Reserved */
    uint32_t res3;      /* 0x010 Reserved */
    uint32_t res4;      /* 0x014 Reserved */
    uint32_t fr;        /* 0x018 Flag Register */
    uint32_t res5;      /* 0x01c Reserved */
    uint32_t ilpr;      /* 0x020 IrDA Low-Power Counter Register */
    uint32_t ibrd;      /* 0x024 Integer Baud Rate Register */
    uint32_t fbrd;      /* 0x028 Fractional Baud Rate Register */
    uint32_t lcr_h;     /* 0x02c Line Control Register */
    uint32_t tcr;       /* 0x030 Control Register */
    uint32_t ifls;      /* 0x034 Interrupt FIFO Level Select Register */
    uint32_t imsc;      /* 0x038 Interrupt Mask Set/Clear Register */
    uint32_t ris;       /* 0x03C Raw Interrupt Status Register */
    uint32_t mis;       /* 0x040 Masked Interrupt Status Register */
    uint32_t icr;       /* 0x044 Interrupt Clear Register */
    uint32_t dmacr;     /* 0x048 DMA Control Register */
    /* The rest of the registers are either reserved or not used */
};

#define PL011_UARTFR_TXFF       (1 << 5)
#define PL011_UARTFR_RXFE       (1 << 4)

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

enum serial_parity {
    PARITY_NONE,
    PARITY_EVEN,
    PARITY_ODD
};

