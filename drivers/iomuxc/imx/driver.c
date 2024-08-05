#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>

uintptr_t iomuxc_base;
uintptr_t uart1_base;

typedef struct iomuxc_config {
    uint32_t mux_reg;     /* Contains offset of mux registers */
    uint32_t conf_reg;    /* Offset of pad configuration register */
    uint32_t input_reg;   /* Offset of select input register */
    uint32_t mux_val;     /* Mux values to be applied */
    uint32_t input_val;   /* Select input values to be applied */
    uint32_t pad_setting; /* Pad configuration values to be applied */
} iomuxc_config_t;

extern iomuxc_config_t iomuxc_configs[1000];
extern uint32_t num_iomuxc_configs;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
#define URXD  0x00 /* UART Receiver Register */
#define UTXD  0x40 /* UART Transmitter Register */
#define UCR1  0x80 /* UART Control Register 1 */
#define UCR2  0x84 /* UART Control Register 2 */
#define UCR3  0x88 /* UART Control Register 3 */
#define UCR4  0x8c /* UART Control Register 4 */
#define UFCR  0x90 /* UART FIFO Control Register */
#define USR1  0x94 /* UART Status Register 1 */
#define USR2  0x98 /* UART Status Register 2 */
#define UESC  0x9c /* UART Escape Character Register */
#define UTIM  0xa0 /* UART Escape Timer Register */
#define UBIR  0xa4 /* UART BRM Incremental Register */
#define UBMR  0xa8 /* UART BRM Modulator Register */
#define UBRC  0xac /* UART Baud Rate Counter Register */
#define ONEMS 0xb0 /* UART One Millisecond Register */
#define UTS   0xb4 /* UART Test Register */

#define UART_SR1_TRDY         BIT(13)
#define UART_SR1_RRDY         BIT(9)
#define UART_SR2_TXFIFO_EMPTY BIT(14)
#define UART_SR2_RXFIFO_RDR   BIT(0)

#define UART_REG(x) ((volatile uint32_t *)(uart1_base + (x)))

void uart_drv_putchar(unsigned char c)
{
    while (!(*UART_REG(USR2) & UART_SR2_TXFIFO_EMPTY));
    *UART_REG(UTXD) = c;
}

unsigned char uart_drv_getchar(void)
{
    while (!(*UART_REG(USR2) & UART_SR2_RXFIFO_RDR));
    return *UART_REG(URXD);
}

void _sddf_putchar(char character)
{
    uart_drv_putchar(character);
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

void init(void) {
    sddf_printf_("iomuxc started\n");
    sddf_printf_("iomuxc nums of config is %llu\n", num_iomuxc_configs);

    sddf_printf_("iomuxc data dump begin...one pin per line\n");
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        sddf_printf_("%u %u %u %u %u %u\n", iomuxc_configs[i].mux_reg, iomuxc_configs[i].conf_reg, iomuxc_configs[i].input_reg, iomuxc_configs[i].mux_val, iomuxc_configs[i].input_val, iomuxc_configs[i].pad_setting);
    }


    sddf_printf_("iomuxc initialising...");
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        uint32_t *mux_reg_offset = iomuxc_base + (uintptr_t) iomuxc_configs[i].mux_reg;
        *mux_reg_offset = iomuxc_configs[i].mux_val;

        uint32_t *conf_reg_offset = iomuxc_base + (uintptr_t) iomuxc_configs[i].conf_reg;
        *conf_reg_offset = iomuxc_configs[i].pad_setting;

        uint32_t *input_reg_offset = iomuxc_base + (uintptr_t) iomuxc_configs[i].input_reg;
        *input_reg_offset = iomuxc_configs[i].input_val;
    }
    sddf_printf_("iomuxc done\n");


}

void notified(microkit_channel ch) {

}
