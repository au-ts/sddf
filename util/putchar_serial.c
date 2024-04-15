#include <microkit.h>

extern uintptr_t uart_base;

#define REG_PTR(offset) ((volatile uint32_t *)((uart_base) + (offset)))

#if defined(CONFIG_PLAT_IMX8MM_EVK) || defined(CONFIG_PLAT_MAAXBOARD)
#define UART_STATUS 0x98
#define TRANSMIT 0x40
#define STAT_TDRE (1 << 14)

void _sddf_putchar(char character)
{
    while (!(*REG_PTR(UART_STATUS) & STAT_TDRE)) { }
    *REG_PTR(TRANSMIT) = character;
}
#elif defined(CONFIG_PLAT_ODROIDC4)
#define UART_STATUS 0xC
#define UART_WFIFO 0x0
#define UART_TX_FULL (1 << 21)

void _sddf_putchar(char character)
{
    while ((*REG_PTR(UART_STATUS) & UART_TX_FULL)) {}
    *REG_PTR(UART_WFIFO) = character & 0x7f;
}
#elif defined(CONFIG_PLAT_QEMU_ARM_VIRT)
#define UARTDR 0x000
#define UARTFR 0x018
#define PL011_UARTFR_TXFF (1 << 5)

void _sddf_putchar(char character)
{
    while ((*REG_PTR(UARTFR) & PL011_UARTFR_TXFF) != 0);
    *REG_PTR(UARTDR) = character;
}
#else
#error "Missing sDDF serial putchar function"
#endif
