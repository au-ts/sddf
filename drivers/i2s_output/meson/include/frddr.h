// "from DDR" FIFO mapping for audio output - Meson S905X3 (ODROID C4)
// Note: this is the abstract interface. See audio.h for register mappings.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
#pragma once

#include <stdint.h>
#include <stdbool.h>


#define FRDDR_SRC_TDMOUT_A 0
#define FRDDR_SRC_TDMOUT_B 1
#define FRDDR_SRC_TDMOUT_C 3
#define FRDDR_SRC_SPDIFOUT 4
#define FRDDR_SRC_SPDIFOUT_B 5

typedef uint32_t ddr_addr_t;


typedef struct frddr_conf {
    uint8_t fifo_depth;
    uint8_t start_write_threshold;
    bool double_buffer;  // If true, enables B buffer for A/B buffering
    uint8_t ack_delay;      // max size 1 << 4
    uint8_t endianness_mask;

    // Source control
    uint8_t share_src;  // Zero if not sharing, otherwise set to channel number of
                        // TDMOUT or SPDIFOUT that shares this FRDDR.
    
    uint8_t src_mask;   // set bits 0-3 to enable respective sources
    uint8_t src0_select; // Select from FRDDR_SRC_X defines
    uint8_t src1_select;
    uint8_t src2_select;

    // Buffer A - primary
    ddr_addr_t start_addr_a;  // start address of buffer A
    ddr_addr_t finish_addr_a; // end address of buffer A

    // Buffer B - only used if double_buffer is true
    ddr_addr_t start_addr_b;  // start address of buffer B
    ddr_addr_t finish_addr_b; // end address of buffer B

    // Other pointers
    ddr_addr_t int_addr;    // intermediate point to throw precompletion interrupt.
                            // if range is outside of start->end, disabled.
    ddr_addr_t init_addr;   // initialise address for buffer A - not the same as start.


} frdddr_conf_t;

typedef enum meson_frddr {
    FRDDR_A,
    FRDDR_B,
    FRDDR_C,
    FRDDR_D
} meson_frddr_t;

typedef struct frddr {
    struct frddr_conf* conf;
    uint8_t id; // FRDDR a, b, c, or d
} frddr_t;

// Struct creation
frddr_t initialise_frddr(frdddr_conf_t *conf, meson_frddr_t id);

// Status reporting
int frddr__get_status(frddr_t *f);
int frddr__get_fifo_count(frddr_t *f);
int frddr__get_interrupt_id(frddr_t *f);
int frddr__get_buff_a_irq_cnt(frddr_t *f);
int frddr__get_buff_b_irq_cnt(frddr_t *f);

// Control
int frddr__enable(frddr_t *f);
int frddr__disable(frddr_t *f);
int frddr__force_finish(frddr_t *f);
int frddr__clear_interrupt_status(frddr_t *f);
int frddr__set_write_threshold(frddt_t *f, uint8_t threshold);
int frddr__set_ack_delay(frddr_t *f, uint8_t delay);

// Buffer control
int frddr__set_init_address(frddr_t *f, ddr_addr_t addr);

int frddr__set_start_address_a(frddr_t *f, ddr_addr_t addr);
int frddr__set_finish_address_a(frddr_t *f, ddr_addr_t addr);
int frddr__set_interrupt_address_a(frddr_t *f, ddr_addr_t addr);

int frddr__set_finish_address_a(frddr_t *f, ddr_addr_t addr);
int frddr__set_start_address_b(frddr_t *f, ddr_addr_t addr);
int frddr__set_interrupt_address_b(frddr_t *f, ddr_addr_t addr);

// Debug
void frddr__debug_status_dump(frddr *f);