// Memory controller interactions - Meson S905X3 (ODROID C4)
// Matt Rossouw (matthew.rossouw@unsw.edu.au)

#include <stdint.h>
#include <stdbool.h>

#define DDR_ARB_BITS_FRDDR_D BITS(7)
#define DDR_ARB_BITS_FRDDR_C BITS(6)
#define DDR_ARB_BITS_FRDDR_B BITS(5)
#define DDR_ARB_BITS_FRDDR_A BITS(4)
#define DDR_ARB_BITS_TODDR_D BITS(3)
#define DDR_ARB_BITS_TODDR_C BITS(2)
#define DDR_ARB_BITS_TODDR_B BITS(1)
#define DDR_ARB_BITS_TODDR_A BITS(0)

typedef struct ddr_arbitration_conf {
    bool arb_enable;
    uint8_t arb_mask;
}