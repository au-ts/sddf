/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/* ----------------- ICMP Protocol Definitions ---------------------------*/

/* Shared ICMP header prefix accross all control types */
typedef struct __attribute__((__packed__)) icmp_hdr {
    /* ICMP type */
    uint8_t type;
    /* ICMP sub-type */
    uint8_t code;
    /* internet checksum calculated over ICMP header and data */
    uint16_t check;
    /* The following 4 bytes of the header are ICMP type dependent */
} icmp_hdr_t;
