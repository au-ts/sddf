/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/bitarray.h>
#include <sddf/util/util.h>

/* Create a bit mask of nbits contiguous bits starting from the least
significant bit*/
#define BITMASK(nbits) ((nbits) ? ~0ull >> (64 - (nbits)): 0ull)

/* Find the index of the word containing the bit_pos bit */
#define WORD_IDX(bit_pos) ((bit_pos) >> 6)

/* Find the index of the bit_pos bit within it's word */
#define BIT_IDX(bit_pos) ((bit_pos) & 63)

void bitarray_init(bitarray_t *bitarr, uint64_t *words, uint64_t num_bits)
{
    bitarr->num_bits = num_bits;
    bitarr->words = words;
}

char bitarray_get_bit(bitarray_t *bitarr, uint64_t index)
{
    assert(index < bitarr->num_bits);
    return (bitarr->words[WORD_IDX(index)] >> BIT_IDX(index)) & 1;
}

typedef enum { ZERO_REGION, FILL_REGION, SWAP_REGION } bitarray_action_t;

static void set_region(bitarray_t *bitarr, uint64_t start, uint64_t length, bitarray_action_t action)
{
    assert(start < bitarr->num_bits && start + length <= bitarr->num_bits);

    if (length == 0) {
        return;
    }

    uint64_t word_idx = WORD_IDX(start);
    uint64_t last_word_idx = WORD_IDX(start + length - 1);
    uint64_t bit_idx = BIT_IDX(start);
    uint64_t last_bit_idx = 63;

    while (word_idx <= last_word_idx) {
        if (word_idx == last_word_idx) {
            last_bit_idx = BIT_IDX(start + length - 1);
        }
        uint64_t mask = BITMASK(last_bit_idx - bit_idx + 1) << bit_idx;

        switch (action) {
        case ZERO_REGION:
            bitarr->words[word_idx] &= ~mask;
            break;
        case FILL_REGION:
            bitarr->words[word_idx] |= mask;
            break;
        case SWAP_REGION:
            bitarr->words[word_idx] ^= mask;
            break;
        }

        word_idx++;
        bit_idx = 0;
    }
}

void bitarray_set_region(bitarray_t *bitarr, uint64_t start, uint64_t len, bool value)
{
    if (value) {
        set_region(bitarr, start, len, FILL_REGION);
    } else {
        set_region(bitarr, start, len, ZERO_REGION);
    }
}

void bitarray_toggle_region(bitarray_t *bitarr, uint64_t start, uint64_t len)
{
    set_region(bitarr, start, len, SWAP_REGION);
}

uint64_t bitarray_count_bits(bitarray_t *bitarr, uint64_t start, bool is_set)
{
    assert(start < bitarr->num_bits);

    uint64_t count = 0;
    uint64_t word_idx = WORD_IDX(start);
    uint64_t last_word_idx = WORD_IDX(bitarr->num_bits - 1);
    uint64_t bit_idx = BIT_IDX(start);
    uint64_t last_bit_idx = 63;

    while (word_idx <= last_word_idx) {

        uint64_t word = bitarr->words[word_idx];

        if (word_idx == last_word_idx) {
            last_bit_idx = BIT_IDX(bitarr->num_bits - 1);
        }

        while (bit_idx <= last_bit_idx) {
            if (((word >> bit_idx) & 1) != is_set) {
                return count;
            }
            count++;
            bit_idx++;
        }

        word_idx++;
        bit_idx = 0;
    }

    return count;
}
