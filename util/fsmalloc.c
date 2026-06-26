/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <sddf/util/bitarray.h>
#include <sddf/util/fsmalloc.h>
#include <sddf/util/util.h>

/**
 * Convert a bit position to the address of the corresponding data cell.
 *
 * @param fsmalloc pointer to the fsmalloc struct.
 * @param bitpos bit position of the data cell
 *
 * @return address of the data cell
 */
static inline uintptr_t bitpos_to_addr(fsmalloc_t *fsmalloc, uint64_t bitpos)
{
    return fsmalloc->base_addr + (uintptr_t)(bitpos * fsmalloc->cell_size);
}

/**
 * Convert an address to the bit position of the corresponding data cell.
 *
 * @param fsmalloc pointer to the fsmalloc struct.
 * @param addr address of the data cell
 *
 * @return bit position of the data cell
 */
static inline uint64_t addr_to_bitpos(fsmalloc_t *fsmalloc, uintptr_t addr)
{
    return (uint64_t)(addr - fsmalloc->base_addr) / fsmalloc->cell_size;
}

void fsmalloc_free(fsmalloc_t *fsmalloc, uintptr_t addr, uint64_t count)
{
    unsigned int start_bitpos = addr_to_bitpos(fsmalloc, addr);

    // Assert that these bits were allocated
    assert(bitarray_count_bits(fsmalloc->avail_bitarr, start_bitpos, false) >= count);

    // Set the next count many bits as available
    bitarray_set_region(fsmalloc->avail_bitarr, start_bitpos, count, true);
}

int fsmalloc_alloc(fsmalloc_t *fsmalloc, uintptr_t *addr, uint64_t count)
{
    if (count == 0 || count > fsmalloc->num_cells) {
        return -1;
    }

    uint64_t curr_bitpos = fsmalloc->avail_bitpos;
    uint64_t searched = 0;
    while (searched < fsmalloc->num_cells) {

        // No space at the end, wrap around
        if (curr_bitpos + count > fsmalloc->num_cells) {
            curr_bitpos = 0;
            searched += fsmalloc->num_cells - curr_bitpos;
        }

        uint64_t free_blocks = bitarray_count_bits(fsmalloc->avail_bitarr, curr_bitpos, true);
        // Allocate blocks, update head
        if (free_blocks >= count) {
            *addr = bitpos_to_addr(fsmalloc, curr_bitpos);

            // Set the next count many bits as unavailable
            bitarray_set_region(fsmalloc->avail_bitarr, curr_bitpos, count, false);

            // Update the bitpos
            fsmalloc->avail_bitpos = (curr_bitpos + count) % fsmalloc->num_cells;
            return 0;
        }

        // Skip past the allocated blocks
        curr_bitpos += free_blocks;
        uint64_t alloced_blocks = bitarray_count_bits(fsmalloc->avail_bitarr, curr_bitpos, false);

        curr_bitpos = (curr_bitpos + alloced_blocks) % fsmalloc->num_cells;
        searched += free_blocks + alloced_blocks;
    }

    return -1;
}

void fsmalloc_init(fsmalloc_t *fsmalloc, uintptr_t base_addr, uint64_t cell_size, uint64_t num_cells,
                   bitarray_t *bitarr, uint64_t *words, size_t num_words)
{
    assert(num_words >= BITS_2_WORDS64(num_cells));

    bitarray_init(bitarr, words, num_cells);

    fsmalloc->avail_bitpos = 0;
    fsmalloc->avail_bitarr = bitarr;
    fsmalloc->base_addr = base_addr;
    fsmalloc->cell_size = cell_size;
    fsmalloc->num_cells = num_cells;

    /* Set all available bits to 1 to indicate all cells are available */
    bitarray_set_region(bitarr, 0, num_cells, true);
}
