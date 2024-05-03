// hard-coded layout while waiting for Ivanv's cool buildsystem tool
#pragma once

#include <stdint.h>
#include <sddf/network/queue.h>
#include "helper.h"

#define NUM_CLIENTS 2
static uint8_t vswitch_conn_topology[2] = {0b11, 0b11};
#define IS_CONN(s,d)    (vswitch_conn_topology[s] >> (NUM_CLIENTS - d))

static uint8_t vswitch_mac_base[6] = {0x52, 0x54, 0x02, 0x00, 0x00, 0x00};

#define TX_CLI0_CH  1
#define RX_CLI0_CH  2

uintptr_t tx_free_cli0;
uintptr_t tx_active_cli0;
uintptr_t rx_free_cli0;
uintptr_t rx_active_cli0;

#define TX_CLI1_CH  3
#define RX_CLI1_CH  4

uintptr_t tx_free_cli1;
uintptr_t tx_active_cli1;
uintptr_t rx_free_cli1;
uintptr_t rx_active_cli1;
