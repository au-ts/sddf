/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <sddf/util/printf.h>

#define PR_MAC802_ADDR  "%x:%x:%x:%x:%x:%x"

/* Expects a *pointer* to a struct ether_hdr */
#define PR_MAC802_ADDR_ARGS(a, dir)     (a)->##dir##->addr[0], \
                                        (a)->##dir##->addr[1], \
                                        (a)->##dir##->addr[2], \
                                        (a)->##dir##->addr[3], \
                                        (a)->##dir##->addr[4], \
                                        (a)->##dir##->addr[5]

#define PR_MAC802_DEST_ADDR_ARGS(a) PR_MAC802_ADDR_ARGS(a, dest)
#define PR_MAC802_SRC_ADDR_ARGS(a) PR_MAC802_ADDR_ARGS(a, src)

#define MAC802_BYTES 6

typedef struct mac_addr {
    uint8_t addr[MAC802_BYTES];
} mac_addr_t;

/* Ethernet packet header */
typedef struct ether_hdr {
    mac_addr_t dest;
    mac_addr_t src;
    uint8_t etype[2]; // Ethertype
} __attribute__((__packed__)) ether_hdr_t;

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
    const uint8_t bcast_macaddr[MAC802_BYTES] = { 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF };
    return mac802_addr_eq(addr, bcast_macaddr);
}
