/*
 * Copyright 2024, UNSW (ABN 57 195 873 179)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <sddf/util/printf.h>

#define PR_MAC802_ADDR  "%x:%x:%x:%x:%x:%x"

/* Expects a *pointer* to a struct ether_addr */
#define PR_MAC802_ADDR_ARGS(a, dir)     (a)->ether_##dir##_addr_octet[0], \
                                        (a)->ether_##dir##_addr_octet[1], \
                                        (a)->ether_##dir##_addr_octet[2], \
                                        (a)->ether_##dir##_addr_octet[3], \
                                        (a)->ether_##dir##_addr_octet[4], \
                                        (a)->ether_##dir##_addr_octet[5]

#define PR_MAC802_DEST_ADDR_ARGS(a) PR_MAC802_ADDR_ARGS(a, dest)
#define PR_MAC802_SRC_ADDR_ARGS(a) PR_MAC802_ADDR_ARGS(a, src)

#define MAC802_BYTES 6

/* This is a name for the 96 bit ethernet addresses available on many
   systems.  */
struct ether_addr {
    uint8_t ether_dest_addr_octet[MAC802_BYTES];
    uint8_t ether_src_addr_octet[MAC802_BYTES];
    uint8_t etype[2]; // Ethertype
    uint8_t payload[46];
    uint8_t crc[4];
} __attribute__ ((__packed__));


static inline bool mac802_addr_eq_num(const uint8_t *addr0, const uint8_t *addr1, unsigned int num)
{
    for (int i = 0; i < num; i++) {
        if (addr0[i] != addr1[i]) {
            return false;
        }
    }
    return true;
}

static inline bool mac802_addr_eq(const uint8_t *addr0, const uint8_t *addr1)
{
    return mac802_addr_eq_num(addr0, addr1, MAC802_BYTES);
}

static inline bool mac802_addr_is_bcast(const uint8_t *addr)
{
    const uint8_t bcast_macaddr[MAC802_BYTES] = {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};
    return mac802_addr_eq(addr, bcast_macaddr);
}
