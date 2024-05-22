#pragma once

#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/network/queue.h>

#define ETHERNET_CLI0_NAME "client0"
#define ETHERNET_CLI1_NAME "client1"
#define ETHERNET_COPY0_NAME "copy0"
#define ETHERNET_COPY1_NAME "copy1"
#define ETHERNET_VIRT_RX_NAME "virt_rx"
#define ETHERNET_VIRT_TX_NAME "virt_tx"
#define ETHERNET_DRIVER_NAME "eth"
#define ETHERNET_TIMER_NAME "timer"

#define ETHERNET_DATA_REGION_SIZE                    0x200000
#define ETHERNET_HW_REGION_SIZE                      0x10000

#define MAC_ADDR_ARP                        0xFFFFFFFFFFFF

#if defined(CONFIG_PLAT_IMX8MM_EVK)
#define MAC_ADDR_CLI0                       0x525401000001
#define MAC_ADDR_CLI1                       0x525401000002
#elif defined(CONFIG_PLAT_ODROIDC4)
#define MAC_ADDR_CLI0                       0x525401000003
#define MAC_ADDR_CLI1                       0x525401000004
#elif defined(CONFIG_PLAT_MAAXBOARD)
#define MAC_ADDR_CLI0                       0x525401000005
#define MAC_ADDR_CLI1                       0x525401000006
#elif defined(CONFIG_PLAT_QEMU_ARM_VIRT)
#define MAC_ADDR_CLI0                       0x525401000007
#define MAC_ADDR_CLI1                       0x525401000008
#else
#error "Must define MAC addresses for clients in ethernet config"
#endif

#define ETHERNET_TX_QUEUE_SIZE_CLI0                   512
#define ETHERNET_TX_QUEUE_SIZE_CLI1                   512
#define ETHERNET_TX_QUEUE_SIZE_DRIV                   (ETHERNET_TX_QUEUE_SIZE_CLI0 + ETHERNET_TX_QUEUE_SIZE_CLI1)

#define ETHERNET_TX_DATA_REGION_SIZE_CLI0            ETHERNET_DATA_REGION_SIZE
#define ETHERNET_TX_DATA_REGION_SIZE_CLI1            ETHERNET_DATA_REGION_SIZE

_Static_assert(ETHERNET_TX_DATA_REGION_SIZE_CLI0 >= ETHERNET_TX_QUEUE_SIZE_CLI0 * NET_BUFFER_SIZE,
                "Client0 TX data region size must fit Client0 TX buffers");
_Static_assert(ETHERNET_TX_DATA_REGION_SIZE_CLI1 >= ETHERNET_TX_QUEUE_SIZE_CLI1 * NET_BUFFER_SIZE, 
                "Client1 TX data region size must fit Client1 TX buffers");

#define ETHERNET_RX_QUEUE_SIZE_DRIV                   512
#define ETHERNET_RX_QUEUE_SIZE_CLI0                   512
#define ETHERNET_RX_QUEUE_SIZE_CLI1                   512
#define ETHERNET_RX_QUEUE_SIZE_COPY0                  ETHERNET_RX_QUEUE_SIZE_DRIV
#define ETHERNET_RX_QUEUE_SIZE_COPY1                  ETHERNET_RX_QUEUE_SIZE_DRIV

#define ETHERNET_RX_DATA_REGION_SIZE_DRIV            ETHERNET_DATA_REGION_SIZE
#define ETHERNET_RX_DATA_REGION_SIZE_CLI0            ETHERNET_DATA_REGION_SIZE
#define ETHERNET_RX_DATA_REGION_SIZE_CLI1            ETHERNET_DATA_REGION_SIZE

_Static_assert(ETHERNET_RX_DATA_REGION_SIZE_DRIV >= ETHERNET_RX_QUEUE_SIZE_DRIV * NET_BUFFER_SIZE, 
                "Driver RX data region size must fit Driver RX buffers");
_Static_assert(ETHERNET_RX_DATA_REGION_SIZE_CLI0 >= ETHERNET_RX_QUEUE_SIZE_CLI0 * NET_BUFFER_SIZE, 
                "Client0 RX data region size must fit Client0 RX buffers");
_Static_assert(ETHERNET_RX_DATA_REGION_SIZE_CLI1 >= ETHERNET_RX_QUEUE_SIZE_CLI1 * NET_BUFFER_SIZE, 
                "Client1 RX data region size must fit Client1 RX buffers");

#define ETHERNET_MAX_QUEUE_SIZE MAX(ETHERNET_TX_QUEUE_SIZE_DRIV, MAX(ETHERNET_RX_QUEUE_SIZE_DRIV, MAX(ETHERNET_RX_QUEUE_SIZE_CLI0, ETHERNET_RX_QUEUE_SIZE_CLI1)))
_Static_assert(ETHERNET_TX_QUEUE_SIZE_DRIV >= ETHERNET_TX_QUEUE_SIZE_CLI0 + ETHERNET_TX_QUEUE_SIZE_CLI1, 
                "Driver TX queue must have capacity to fit all of client's TX buffers.");
_Static_assert(ETHERNET_RX_QUEUE_SIZE_COPY0 >= ETHERNET_RX_QUEUE_SIZE_DRIV, 
                "Copy0 queues must have capacity to fit all RX buffers.");
_Static_assert(ETHERNET_RX_QUEUE_SIZE_COPY1 >= ETHERNET_RX_QUEUE_SIZE_DRIV, 
                "Copy1 queues must have capacity to fit all RX buffers.");
_Static_assert(sizeof(net_queue_t) + ETHERNET_MAX_QUEUE_SIZE * sizeof(net_buff_desc_t) <= ETHERNET_DATA_REGION_SIZE, "net_queue_t must fit into a single data region.");

static inline bool __ethernet_str_match(const char *s0, const char *s1)
{
    while (*s0 != '\0' && *s1 != '\0' && *s0 == *s1) {
        s0++, s1++;
    }
    return *s0 == *s1;
}

static void __ethernet_set_mac_addr(uint8_t *mac, uint64_t val)
{
    mac[0] = val >> 40 & 0xff;
    mac[1] = val >> 32 & 0xff;
    mac[2] = val >> 24 & 0xff;
    mac[3] = val >> 16 & 0xff;
    mac[4] = val >> 8 & 0xff;
    mac[5] = val & 0xff;
}

static inline void ethernet_cli_mac_addr_init_sys(char *pd_name, uint8_t *macs)
{
    if (__ethernet_str_match(pd_name, ETHERNET_CLI0_NAME)) {
        __ethernet_set_mac_addr(macs, MAC_ADDR_CLI0);
    } else if (__ethernet_str_match(pd_name, ETHERNET_CLI1_NAME)) {
        __ethernet_set_mac_addr(macs, MAC_ADDR_CLI1);
    } 
}

static inline void ethernet_virt_mac_addr_init_sys(char *pd_name, uint8_t *macs)
{
    if (__ethernet_str_match(pd_name, ETHERNET_VIRT_RX_NAME)) {
        __ethernet_set_mac_addr(macs, MAC_ADDR_CLI0);
        __ethernet_set_mac_addr(&macs[ETH_HWADDR_LEN], MAC_ADDR_CLI1);
    }
}

static inline void ethernet_cli_queue_init_sys(char *pd_name, net_queue_handle_t *rx_queue, uintptr_t rx_free, 
                                                uintptr_t rx_active, net_queue_handle_t *tx_queue, uintptr_t tx_free, 
                                                uintptr_t tx_active)
{
    if (__ethernet_str_match(pd_name, ETHERNET_CLI0_NAME)) {
        net_queue_init(rx_queue, (net_queue_t *) rx_free, (net_queue_t *) rx_active, ETHERNET_RX_QUEUE_SIZE_CLI0);
        net_queue_init(tx_queue, (net_queue_t *) tx_free, (net_queue_t *) tx_active, ETHERNET_TX_QUEUE_SIZE_CLI0);
    } else if (__ethernet_str_match(pd_name, ETHERNET_CLI1_NAME)) {
        net_queue_init(rx_queue, (net_queue_t *) rx_free, (net_queue_t *) rx_active, ETHERNET_RX_QUEUE_SIZE_CLI1);
        net_queue_init(tx_queue, (net_queue_t *) tx_free, (net_queue_t *) tx_active, ETHERNET_TX_QUEUE_SIZE_CLI1);
    }
}

static inline void ethernet_copy_queue_init_sys(char *pd_name, net_queue_handle_t *cli_queue, uintptr_t cli_free, 
                                                uintptr_t cli_active, net_queue_handle_t *virt_queue, uintptr_t virt_free, 
                                                uintptr_t virt_active)
{
    if (__ethernet_str_match(pd_name, ETHERNET_COPY0_NAME)) {
        net_queue_init(cli_queue, (net_queue_t *) cli_free, (net_queue_t *) cli_active, ETHERNET_RX_QUEUE_SIZE_CLI0);
        net_queue_init(virt_queue, (net_queue_t *) virt_free, (net_queue_t *) virt_active, ETHERNET_RX_QUEUE_SIZE_COPY0);
    } else if (__ethernet_str_match(pd_name, ETHERNET_COPY1_NAME)) {
        net_queue_init(cli_queue, (net_queue_t *) cli_free, (net_queue_t *) cli_active, ETHERNET_RX_QUEUE_SIZE_CLI1);
        net_queue_init(virt_queue, (net_queue_t *) virt_free, (net_queue_t *) virt_active, ETHERNET_RX_QUEUE_SIZE_COPY1);
    }
}

static inline void ethernet_virt_queue_init_sys(char *pd_name, net_queue_handle_t *cli_queue, uintptr_t cli_free, uintptr_t cli_active)
{
    if (__ethernet_str_match(pd_name, ETHERNET_VIRT_RX_NAME)) {
        net_queue_init(cli_queue, (net_queue_t *) cli_free, (net_queue_t *) cli_active, ETHERNET_RX_QUEUE_SIZE_COPY0);
        net_queue_init(&cli_queue[1], (net_queue_t *) (cli_free + 2 * ETHERNET_DATA_REGION_SIZE), 
                        (net_queue_t *) (cli_active + 2 * ETHERNET_DATA_REGION_SIZE), ETHERNET_RX_QUEUE_SIZE_COPY1);
    } else if (__ethernet_str_match(pd_name, ETHERNET_VIRT_TX_NAME)) {
        net_queue_init(cli_queue, (net_queue_t *) cli_free, (net_queue_t *) cli_active, ETHERNET_TX_QUEUE_SIZE_CLI0);
        net_queue_init(&cli_queue[1], (net_queue_t *) (cli_free + 2 * ETHERNET_DATA_REGION_SIZE), 
                        (net_queue_t *) (cli_active + 2 * ETHERNET_DATA_REGION_SIZE), ETHERNET_TX_QUEUE_SIZE_CLI1);
    }
}

static inline void ethernet_mem_region_init_sys(char *pd_name, uintptr_t *mem_regions, uintptr_t start_region) {
    if (__ethernet_str_match(pd_name, ETHERNET_VIRT_TX_NAME)) {
        mem_regions[0] = start_region;
        mem_regions[1] = start_region + ETHERNET_DATA_REGION_SIZE;
    }
}
