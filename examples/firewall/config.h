#pragma once

#include <microkit.h>
#include <stdbool.h>
#include <stdint.h>
#include <sddf/resources/common.h>
#include <sddf/resources/device.h>

#define LIONS_FS_MAGIC_LEN 8
static char LIONS_FS_MAGIC[LIONS_FS_MAGIC_LEN] = { 'L', 'i', 'o', 'n', 's', 'O', 'S', 0x3 };

typedef struct arp_router_connection_resource {
    region_resource_t arp_queue;
    region_resource_t arp_cache;
    uint8_t id;
} arp_router_connection_resource_t;

typedef struct arp_requester_config {
    char magic[LIONS_FS_MAGIC_LEN];
    arp_router_connection_resource_t router;
    uint8_t mac_addr[ETH_HWADDR_LEN];
} arp_requester_config_t;

typedef struct arp_responder_config {
    char magic[LIONS_FS_MAGIC_LEN];
    uint32_t ip;
    uint8_t mac_addr[ETH_HWADDR_LEN];
} arp_responder_config_t;

/* @kwinter: This is the same as the arp requester for now,
 but will change in the future when we need to connect it with
 all the different filters. */
typedef struct router_config {
    char magic[LIONS_FS_MAGIC_LEN];
    arp_router_connection_resource_t router;
    uint8_t mac_addr[ETH_HWADDR_LEN];
} router_config_t;