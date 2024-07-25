// "from DDR" FIFO mapping for audio output - Meson S905X3 (ODROID C4)
// Matt Rossouw (matthew.rossouw@unsw.edu.au)

#include <sddf/i2s_audio_output/frddr.h>
#include <sddf/i2s_audio_output/ddrctrl.h>
#include <sddf/i2s_audio_output/audio.h>

#define REGISTER *(volatile uint32_t *)

/**
 * Return register offset for one of the 4 meson FRDDRs.
 */
static inline uintptr_t frddr_offset(meson_frddr_t t) {
    return (uintptr_t)((t * FRDDR_REG_ID_OFFSET) + AUDIO_BASE);
}

/**
 * Initialise an FRDDR and return a handle.
 * Arguments:
 *  conf: pointer to populated configuration struct
 *    id: Device to initialise - FRDDR A, B, C or D.
 */
frddr_t initialise_frddr(frdddr_conf_t *conf, meson_frddr_t id) {
    frddr_t ret = {
        conf, id
    };

    // Get registers
    uintptr_t reg_offset = frddr_offset(id);
    volatile uint32_t ctrl0 = REGISTER(reg_offset + FRDDR_REG_CTRL0);
    volatile uint32_t ctrl1 = REGISTER(reg_offset + FRDDR_REG_CTRL1);
    volatile uint32_t start_a = REGISTER(reg_offset + FRDDR_REG_START_ADDR);
    volatile uint32_t start_b = REGISTER(reg_offset + FRDDR_REG_START_ADDRB);
    volatile uint32_t end_a = REGISTER(reg_offset + FRDDR_REG_FINISH_ADDR);
    volatile uint32_t end_b = REGISTER(reg_offset + FRDDR_REG_FINISH_ADDR);
    volatile uint32_t interrupt = REGISTER(reg_offset + FRDDR_REG_INT_ADDR);
    volatile uint32_t init = REGISTER(reg_offset + FRDDR_REG_INIT_ADDR);

    // Set whole-register values first
    init = conf->init_addr;
    interrupt = conf->int_addr;
    start_a = conf->start_addr_a;
    start_b = conf->start_addr_b;
    end_a = conf->finish_addr_a;
    end_b = conf->finish_addr_b;

    // Set up ctrl registers
    uint32_t ctrl0_tmp = 0x0;
    if (conf->double_buffer) ctrl0_tmp |= FRDDR_REG_CTRL0_PP_MD;
    assert(conf->endianness_mask <= 0b111);
    ctrl0_tmp |= endianness_mask << 24;
    
    
    assert(fifo_depth <= 0b111);
    

}