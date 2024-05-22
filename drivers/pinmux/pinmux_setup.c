#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>

#define PINMUX_MAX  1000

/* The below structure is specifically for the imx8mm */
/* NOTE: all of the values at a particular index for each of these arrays are for the same device */
/* i.e. NO device would not have any info for any of the below properties */

struct pinmux_config {
    int n; /* Number of entries to configure */
    uint32_t mux_reg[PINMUX_MAX]; /* Contains offset of mux registers */
    uint32_t conf_reg[PINMUX_MAX]; /* Offset of pad configuration register */
    uint32_t input_reg[PINMUX_MAX]; /* Offset of select input register */
    uint32_t mux_val[PINMUX_MAX]; /* Mux values to be applied */
    uint32_t input_val[PINMUX_MAX]; /* Select input values to be applied */
    uint32_t pad_setting[PINMUX_MAX]; /* Pad configuration values to be applied */
};

uintptr_t pinmux_base;

extern struct pinmux_config conf;

void init(void) 
{
    sddf_dprintf("Starting pinmux init\n");
    for (int i = 0; i < conf.n; i ++) {
        sddf_printf("%d ", conf.mux_reg[i]);
    }
    sddf_dprintf("\n");
    sddf_dprintf("Pinmux init complete\n");
    
}

void notified(microkit_channel ch) 
{
    sddf_dprintf("I've been notified\n");
}