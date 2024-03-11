#pragma once

#include <stdint.h>

#define ETH_TYPE_ARP 0x0806U
#define ETH_TYPE_IP 0x0800U
#define ETH_HWADDR_LEN 6
#define ETHARP_OPCODE_REQUEST 1
#define ETHARP_OPCODE_REPLY 2

#define MAX_BUFFS 1536
#define BUFF_SIZE 2048

struct ethernet_address {
  uint8_t addr[6];
} __attribute__((packed));

struct ethernet_header {
  struct ethernet_address dest;
  struct ethernet_address src;
  uint16_t type;
} __attribute__((packed));
