
/* SPDX-License-Identifier: GPL-2.0 */
/*
 *  Copyright (c) 2010-2011 Jeremy Kerr <jeremy.kerr@canonical.com>
 *  Copyright (C) 2011-2012 Linaro Ltd <mturquette@linaro.org>
 *
 *  This file is derived from:
 *    https://github.com/torvalds/linux/blob/6485cf5ea253d40d507cd71253c9568c5470cd27/include/linux/clk-provider.h
 */

#pragma once

#include <stdint.h>

/*
 * flags used across common struct clk.  these flags should only affect the
 * top-level framework.  custom flags for dealing with hardware specifics
 * belong in struct clk_foo
 */
#define CLK_SET_RATE_GATE    BIT(0) /* must be gated across rate change */
#define CLK_SET_PARENT_GATE    BIT(1) /* must be gated across re-parent */
#define CLK_SET_RATE_PARENT    BIT(2) /* propagate rate change up one level */
#define CLK_IGNORE_UNUSED    BIT(3) /* do not gate even if unused */
                /* unused */
                /* unused */
#define CLK_GET_RATE_NOCACHE    BIT(6) /* do not use the cached clk rate */
#define CLK_SET_RATE_NO_REPARENT BIT(7) /* don't re-parent on rate change */
#define CLK_GET_ACCURACY_NOCACHE BIT(8) /* do not use the cached clk accuracy */
#define CLK_RECALC_NEW_RATES    BIT(9) /* recalc rates after notifications */
#define CLK_SET_RATE_UNGATE    BIT(10) /* clock needs to run to set rate */
#define CLK_IS_CRITICAL        BIT(11) /* do not gate, ever */
/* parents need enable during gate/ungate, set rate and re-parent */
#define CLK_OPS_PARENT_ENABLE    BIT(12)
/* duty cycle call may be forwarded to the parent clock */
#define CLK_DUTY_CYCLE_PARENT    BIT(13)

#define CLK_GATE_SET_TO_DISABLE        BIT(0)
#define CLK_GATE_HIWORD_MASK        BIT(1)
#define CLK_GATE_BIG_ENDIAN        BIT(2)

#define CLK_DIVIDER_ONE_BASED        BIT(0)
#define CLK_DIVIDER_POWER_OF_TWO    BIT(1)
#define CLK_DIVIDER_ALLOW_ZERO        BIT(2)
#define CLK_DIVIDER_HIWORD_MASK        BIT(3)
#define CLK_DIVIDER_ROUND_CLOSEST    BIT(4)
#define CLK_DIVIDER_READ_ONLY        BIT(5)
#define CLK_DIVIDER_MAX_AT_ZERO        BIT(6)
#define CLK_DIVIDER_BIG_ENDIAN        BIT(7)

#define CLK_MUX_INDEX_ONE        BIT(0)
#define CLK_MUX_INDEX_BIT        BIT(1)
#define CLK_MUX_HIWORD_MASK        BIT(2)
#define CLK_MUX_READ_ONLY        BIT(3) /* mux can't be changed */
#define CLK_MUX_ROUND_CLOSEST        BIT(4)
#define CLK_MUX_BIG_ENDIAN        BIT(5)

#define CLK_FRAC_DIVIDER_ZERO_BASED        BIT(0)
#define CLK_FRAC_DIVIDER_BIG_ENDIAN        BIT(1)
#define CLK_FRAC_DIVIDER_POWER_OF_TWO_PS   BIT(2)

struct clk;
struct clk_hw;
struct clk_init_data;

/**
 * struct clk_hw - handle for traversing from a struct clk to its corresponding
 * hardware-specific structure. struct clk_hw should be declared within struct
 * clk_foo and then referenced by the struct clk instance that uses struct
 * clk_foo's clk_ops
 *
 * @init: pointer to struct clk_init_data that contains the init data shared
 * with the common clock framework. This pointer will be set to NULL once
 * a clk_register() variant is called on this clk_hw pointer.
 */
struct clk_hw {
    struct clk *clk;
    struct clk_init_data *init;
};

/**
 * struct clk_ops -  Callback operations for hardware clocks; these are to
 * be provided by the clock implementation, and will be called by drivers
 * through the clk_* api.
 *
 * @prepare:    Prepare the clock for enabling. This must not return until
 *        the clock is fully prepared, and it's safe to call clk_enable.
 *        This callback is intended to allow clock implementations to
 *        do any initialisation that may sleep. Called with
 *        prepare_lock held.
 *
 * @unprepare:    Release the clock from its prepared state. This will typically
 *        undo any work done in the @prepare callback. Called with
 *        prepare_lock held.
 *
 * @is_prepared: Queries the hardware to determine if the clock is prepared.
 *        This function is allowed to sleep. Optional, if this op is not
 *        set then the prepare count will be used.
 *
 * @enable:    Enable the clock atomically. This must not return until the
 *        clock is generating a valid clock signal, usable by consumer
 *        devices. Called with enable_lock held. This function must not
 *        sleep.
 *
 * @disable:    Disable the clock atomically. Called with enable_lock held.
 *        This function must not sleep.
 *
 * @is_enabled:    Queries the hardware to determine if the clock is enabled.
 *        This function must not sleep. Optional, if this op is not
 *        set then the enable count will be used.
 *
 * @disable_unused: Disable the clock atomically.  Only called from
 *        clk_disable_unused for gate clocks with special needs.
 *        Called with enable_lock held.  This function must not
 *        sleep.
 *
 * @recalc_rate: Recalculate the rate of this clock, by querying hardware. The
 *        parent rate is an input parameter.  It is up to the caller to
 *        ensure that the prepare_mutex is held across this call. If the
 *        driver cannot figure out a rate for this clock, it must return
 *        0. Returns the calculated rate. Optional, but recommended - if
 *        this op is not set then clock rate will be initialized to 0.
 *
 * @round_rate:    Given a target rate as input, returns the closest rate actually
 *        supported by the clock. The parent rate is an input/output
 *        parameter.
 *
 * @determine_rate: Given a target rate as input, returns the closest rate
 *        actually supported by the clock, and optionally the parent clock
 *        that should be used to provide the clock rate.
 *
 * @set_parent:    Change the input source of this clock; for clocks with multiple
 *        possible parents specify a new parent by passing in the index
 *        as a u8 corresponding to the parent in either the .parent_names
 *        or .parents arrays.  This function in affect translates an
 *        array index into the value programmed into the hardware.
 *        Returns 0 on success, -EERROR otherwise.
 *
 * @get_parent:    Queries the hardware to determine the parent of a clock.  The
 *        return value is a u8 which specifies the index corresponding to
 *        the parent clock.  This index can be applied to either the
 *        .parent_names or .parents arrays.  In short, this function
 *        translates the parent value read from hardware into an array
 *        index.  Currently only called when the clock is initialized by
 *        __clk_init.  This callback is mandatory for clocks with
 *        multiple parents.  It is optional (and unnecessary) for clocks
 *        with 0 or 1 parents.
 *
 * @set_rate:    Change the rate of this clock. The requested rate is specified
 *        by the second argument, which should typically be the return
 *        of .round_rate call.  The third argument gives the parent rate
 *        which is likely helpful for most .set_rate implementation.
 *        Returns 0 on success, -EERROR otherwise.
 *
 * @init:    Perform platform-specific initialization magic.
 *        This is not used by any of the basic clock types.
 *        This callback exist for HW which needs to perform some
 *        initialisation magic for CCF to get an accurate view of the
 *        clock. It may also be used dynamic resource allocation is
 *        required. It shall not used to deal with clock parameters,
 *        such as rate or parents.
 *        Returns 0 on success, -EERROR otherwise.
 *
 */
struct clk_ops {
    uint8_t (*get_parent)(const struct clk *clk);
    int (*set_parent)(struct clk *clk, uint8_t index);
    unsigned long (*recalc_rate)(const struct clk *clk, unsigned long parent_rate);
    int (*set_rate)(const struct clk *clk, uint32_t rate, uint32_t parent_rate);
    void (*init)(struct clk *clk);
    int (*enable)(struct clk *clk);
    int (*disable)(struct clk *clk);
    int (*is_enabled)(struct clk *clk);
};

struct clk {
    struct clk_hw hw;
    void *data;
    uint64_t base;
};

/**
 * struct clk_parent_data - clk parent information
 * @hw: parent clk_hw pointer (used for clk providers with internal clks)
 * @name: globally unique parent name (used as a fallback)
 */
struct clk_parent_data {
    const struct clk *clk;
    const char *name;
};

/**
 * struct clk_init_data - holds init data that's common to all clocks and is
 * shared between the clock provider and the common clock framework.
 *
 * @name: clock name
 * @ops: operations this clock supports
 * @parent_names: array of string names for all possible parents
 * @parent_data: array of parent data for all possible parents (when some
 *               parents are external to the clk controller)
 * @parent_clks: array of pointers to all possible parents (when all parents
 *              are internal to the clk controller)
 * @num_parents: number of possible parents
 * @flags: framework-level hints and quirks
 */
struct clk_init_data {
    uint32_t num_parents;
    uint32_t flags;
    const char *name;
    const struct clk_ops *ops;
    const struct clk **parent_clks;
    const struct clk_parent_data *parent_data;
};

/**
 * struct clk_source_data -  clock source data
 *
 * @rate: ouput rate of clock hardware
 *
 */
struct clk_source_data {
    uint64_t rate;
};

/**
 * struct clk_gate_data - gate specific data
 *
 * @offset:    offset of the register controlling gate
 * @bit_idx:    single bit controlling gate
 * @flags:    hardware-specific flags
 *
 * Flags:
 * CLK_GATE_SET_TO_DISABLE - by default this clock sets the bit at bit_idx to
 *    enable the clock.  Setting this flag does the opposite: setting the bit
 *    disable the clock and clearing it enables the clock
 * CLK_GATE_HIWORD_MASK - The gate settings are only in lower 16-bit
 *    of this register, and mask of gate bits are in higher 16-bit of this
 *    register.  While setting the gate bits, higher 16-bit should also be
 *    updated to indicate changing gate bits.
 * CLK_GATE_BIG_ENDIAN - by default little endian register accesses are used for
 *    the gate register.  Setting this flag makes the register accesses big
 *    endian.
 */
struct clk_gate_data {
    uint32_t offset;
    uint8_t bit_idx;
    uint8_t flags;
};

/**
 * struct clk_div_data - adjustable divider clock
 *
 * @reg:    register containing the divider
 * @shift:  shift to the divider bit field
 * @width:  width of the divider bit field
 * @table:  array of value/divider pairs, last entry should have div = 0
 * @lock:   register lock
 *
 * Clock with an adjustable divider affecting its output frequency.  Implements
 * .recalc_rate, .set_rate and .round_rate
 *
 * @flags:
 * CLK_DIVIDER_ONE_BASED - by default the divisor is the value read from the
 *    register plus one.  If CLK_DIVIDER_ONE_BASED is set then the divider is
 *    the raw value read from the register, with the value of zero considered
 *    invalid, unless CLK_DIVIDER_ALLOW_ZERO is set.
 * CLK_DIVIDER_POWER_OF_TWO - clock divisor is 2 raised to the value read from
 *    the hardware register
 * CLK_DIVIDER_ALLOW_ZERO - Allow zero divisors.  For dividers which have
 *    CLK_DIVIDER_ONE_BASED set, it is possible to end up with a zero divisor.
 *    Some hardware implementations gracefully handle this case and allow a
 *    zero divisor by not modifying their input clock
 *    (divide by one / bypass).
 * CLK_DIVIDER_HIWORD_MASK - The divider settings are only in lower 16-bit
 *    of this register, and mask of divider bits are in higher 16-bit of this
 *    register.  While setting the divider bits, higher 16-bit should also be
 *    updated to indicate changing divider bits.
 * CLK_DIVIDER_ROUND_CLOSEST - Makes the best calculated divider to be rounded
 *    to the closest integer instead of the up one.
 * CLK_DIVIDER_READ_ONLY - The divider settings are preconfigured and should
 *    not be changed by the clock framework.
 * CLK_DIVIDER_MAX_AT_ZERO - For dividers which are like CLK_DIVIDER_ONE_BASED
 *    except when the value read from the register is zero, the divisor is
 *    2^width of the field.
 * CLK_DIVIDER_BIG_ENDIAN - By default little endian register accesses are used
 *    for the divider register.  Setting this flag makes the register accesses
 *    big endian.
 */
struct clk_div_data {
    uint32_t offset;
    uint8_t shift;
    uint8_t width;
    uint8_t flags;
    /* const struct clk_div_table *table; */
};

/**
 * struct clk_fixed_factor_data - fixed multiplier and divider clock
 *
 * @mult:    multiplier
 * @div:    divider
 * @flags:    behavior modifying flags
 *
 * Clock with a fixed multiplier and divider. The output frequency is the
 * parent clock rate divided by div and multiplied by mult.
 * Implements .recalc_rate, .set_rate, .round_rate and .recalc_accuracy
 *
 * Flags:
 * * CLK_FIXED_FACTOR_FIXED_ACCURACY - Use the value in @acc instead of the
 *                                     parent clk accuracy.
 */
struct clk_fixed_factor_data {
    uint32_t mult;
    uint32_t div;
    uint8_t flags;
};

/**
 * struct clk_mux_data - multiplexer clock
 *
 * @reg:    register controlling multiplexer
 * @table:  array of register values corresponding to the parent index
 * @shift:  shift to multiplexer bit field
 * @mask:   mask of mutliplexer bit field
 * @flags:  hardware-specific flags
 * @lock:   register lock
 *
 * Clock with multiple selectable parents.  Implements .get_parent, .set_parent
 * and .recalc_rate
 *
 * Flags:
 * CLK_MUX_INDEX_ONE - register index starts at 1, not 0
 * CLK_MUX_INDEX_BIT - register index is a single bit (power of two)
 * CLK_MUX_HIWORD_MASK - The mux settings are only in lower 16-bit of this
 *    register, and mask of mux bits are in higher 16-bit of this register.
 *    While setting the mux bits, higher 16-bit should also be updated to
 *    indicate changing mux bits.
 * CLK_MUX_READ_ONLY - The mux registers can't be written, only read in the
 *     .get_parent clk_op.
 * CLK_MUX_ROUND_CLOSEST - Use the parent rate that is closest to the desired
 *    frequency.
 * CLK_MUX_BIG_ENDIAN - By default little endian register accesses are used for
 *    the mux register.  Setting this flag makes the register accesses big
 *    endian.
 */
struct clk_mux_data {
    uint32_t offset;
    uint32_t *table;
    uint32_t mask;
    uint8_t shift;
    uint8_t flags;
};

/**
 * function clk_probe() - initialise all clocks
 *
 * @clk_list:    array of pointers to the clocks on SoC
 *
 * All parent clocks will be parsed by name and bound to the struct clk
 */
void clk_probe(struct clk *clk_list[]);

/**
 * function get_parent() - get the current parent clk
 *
 * @clk:    pointer to the current clk
 */
const struct clk *get_parent(const struct clk *clk);

/**
 * function clk_get_rate() - get the rate of target clock
 *
 * @clk:    pointer to the current clk
 *
 */
unsigned long clk_get_rate(const struct clk *clk);

/**
 * function clk_enable() - enable the target clock signal
 *
 * @clk:    pointer to the current clk
 */
uint32_t clk_enable(struct clk *clk);

/**
 * function clk_disable() - disable the target clock signal
 *
 * @clk:    pointer to the current clk
 */
uint32_t clk_disable(struct clk *clk);

/**
 * function clk_set_rate() - set the nearest rate to the requested rate for
 * the target clock
 *
 * @clk:    pointer to the current clk
 */
uint32_t clk_set_rate(struct clk *clk, uint32_t rate);
