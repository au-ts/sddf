/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <sddf/tmu/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#define DEBUG_TMU_DRIVER
#ifdef DEBUG_TMU_DRIVER
#define LOG_TMU_DRIVER(...) do{ sddf_dprintf("TMU DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_TMU_DRIVER(...) do{}while(0)
#endif

#define LOG_TMU_DRIVER_ERR(...) do{ sddf_dprintf("TMU DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)


// TODO: we should extract this quantisation logic to a library. This is really similar
// to what is currently done in timers, i2c and more. The only difference here is that we
// use float, but that just means we need a float and non-float variant.
static inline sddf_temp_celsius_t find_quantised_unit(sddf_temp_celsius_t min_temp,
                                                      sddf_temp_celsius_t max_temp,
                                                      uint32_t quantisation) {
    assert(min_temp < max_temp);

    // calculate value of a unit in this quantisation
    // invariant: range is positive
    sddf_temp_celsius_t range = max_temp - min_temp;
    sddf_temp_celsius_t unit = range / (1 << quantisation);
    assert(unit != 0);
    return unit;
}


/**
 *  Given a temperature in degrees, return a quantised value to put in a device register.
 *  Args:
 *  val_degrees: temperature in degrees
 *  min_temp: minimum temperature represented in register
 *  max_temp: maximum temperature represented in register
 *  quantisation: number of bits used to represent value in hardware
 *  quantised_val: pointer to output
 *
 *  Returns:
 *  sddf_tmu_err_t OK if fine, otherwise positive error value.
 */
sddf_tmu_err_t degrees_to_quantised(sddf_temp_celsius_t val_degrees, sddf_temp_celsius_t min_temp,
                                    sddf_temp_celsius_t max_temp, uint32_t quantisation,
                                    uint64_t *quantised_val) {
    // Sanity: reject values that are invalid
    if (val_degrees < min_temp || val_degrees > max_temp) {
        return SDDF_TMU_ERR_EINVAL;
    }

    sddf_temp_celsius_t unit = find_quantised_unit(min_temp, max_temp, quantisation);

    // convert input temperature to unit
    uint64_t val_in_units = (uint64_t)(val_degrees / unit);

    // if this doesn't fit in the register, we've made a mistake
    assert(val_in_units <= (1 << quantisation));

    *quantised_val = val_in_units;
    return SDDF_TMU_ERR_OK;
}

/**
 *  Given a temperature in quantised units, return a value in degrees celsius.
 *  Args:
 *  val_quantised: temperature in device register units
 *  min_temp: minimum temperature represented in register
 *  max_temp: maximum temperature represented in register
 *  quantisation: number of bits used to represent value in hardware
 *  degrees_celsius: pointer to output
 *
 *  Returns:
 *  sddf_tmu_err_t OK if fine, otherwise positive error value.
 */
sddf_tmu_err_t quantised_to_degrees(uint64_t val_quantised, sddf_temp_celsius_t min_temp,
                                    sddf_temp_celsius_t max_temp, uint32_t quantisation,
                                    sddf_temp_celsius_t *degrees_celsius) {

    sddf_temp_celsius_t unit = find_quantised_unit(min_temp, max_temp, quantisation);

    // convert input quantisation to celsius
    sddf_temp_celsius_t temp = ((sddf_temp_celsius_t)val_quantised * unit);

    // Sanity: if this temperature is outside of the valid temp range we have failed horribly.
    assert(temp > min_temp && temp <= max_temp);

    // Finally: return.
    *degrees_celsius = temp;
    return SDDF_TMU_ERR_OK;
}
