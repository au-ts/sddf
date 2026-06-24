/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

/**
 * This file provides functions and macros to manipulate bit arrays efficiently.
 * In a bit array, the bits are stored in a sequence of words, where each word is typically a machine word
 * (e.g., 32 bits or 64 bits). This implementation uses 64 bits.
 */

/**
 * Rounds up the number of bits to the nearest number of 64-bit words.
 *
 * @param bits The number of bits.
 * @return The number of 64-bit words.
 */
#define BITS_2_WORDS64(bits) (((bits)+63)/64)

typedef struct bitarray {
    uint64_t num_bits; /* Total number of bits */
    uint64_t *words; /* Word array */
} bitarray_t;

/**
 * Initialise a bit array.
 *
 * @param bitarr pointer to the bitarray struct.
 * @param words pointer to the word array.
 * @param num_of_bits number of bits in the word array.
 */
void bitarray_init(bitarray_t *bitarr, uint64_t *words, uint64_t num_bits);

/**
 * Get the value of a specific bit in the bit array.
 *
 * @param bitarr pointer to the bitarray struct.
 * @param index index of the bit to get.
 *
 * @return the value of the bit (0 or 1).
 */
char bitarray_get_bit(bitarray_t *bitarr, uint64_t index);

/**
 * Set all the bits to 0 or 1 in a specific region of the bit array.
 *
 * @param bitarr pointer to the bitarray struct.
 * @param start starting index of the region.
 * @param len length of the region.
 * @param value true sets the bits to 1, false sets the bits to 0.
 */
void bitarray_set_region(bitarray_t *bitarr, uint64_t start, uint64_t len, bool value);

/**
 * Toggle all the bits in a specific region of the bit array.
 *
 * @param bitarr pointer to the bitarray struct.
 * @param start starting index of the region.
 * @param len length of the region.
 */
void bitarray_toggle_region(bitarray_t *bitarr, uint64_t start, uint64_t len);

/**
 * Count the number of contiguous bits set to 0 or 1 starting from the start bit.
 *
 * @param bitarr pointer to the bitarray struct.
 * @param start bit to start counting from.
 * @param is_set true counts the bits set to 1, false counts the bits set to 0.
 *
 * @return number of contiguous bits starting from start having the value provided.
 */
uint64_t bitarray_count_bits(bitarray_t *bitarr, uint64_t start, bool is_set);
