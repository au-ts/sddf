/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <os/sddf.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/network/lib_sddf_lwip.h>
#include <sddf/network/queue.h>
#include <sddf/network/util.h>
#include <sddf/timer/client.h>
#include "lwip/err.h"
#include "lwip/init.h"
#include "lwip/ip4_addr.h"
#include "netif/etharp.h"
#include "lwip/pbuf.h"
#include "lwip/netif.h"
#include "lwip/snmp.h"
#include "lwip/sys.h"
#include "lwip/timeouts.h"
#include "lwip/dhcp.h"

static char SDDF_LIB_SDDF_LWIP_MAGIC[SDDF_LIB_SDDF_LWIP_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x8 };

typedef struct lwip_state {
    /* LWIP network interface struct. */
    struct netif netif;
    /* MAC address of client. */
    uint8_t mac[6];
    /* Output function used to print error messages. */
    sddf_lwip_err_output_fn err_output;
    /* Callback function to be invoked when ip address is obtained. */
    sddf_lwip_netif_status_callback_fn netif_callback;
    /* Function that optionally handles when no free tx buffers available. */
    sddf_lwip_handle_empty_tx_free_fn handle_empty_tx_free;
} lwip_state_t;

typedef struct sddf_state {
    /* sddf net rx queue handle. */
    net_queue_handle_t rx_queue;
    /* sddf net tx queue handle. */
    net_queue_handle_t tx_queue;
    /* sddf channel for net rx virt. */
    sddf_channel rx_ch;
    /* sddf channel for net tx virt. */
    sddf_channel tx_ch;
    /* Base address of data region containing rx buffers. */
    uintptr_t rx_buffer_data_region;
    /* Base address of data region containing tx buffers. */
    uintptr_t tx_buffer_data_region;
    /* Boolean indicating whether buffers have been given to rx virt. */
    bool notify_rx;
    /* Boolean indicating whether buffers have been given to tx virt. */
    bool notify_tx;
    /* sddf channel for timer. */
    sddf_channel timer_ch;
} sddf_state_t;

/* Wrapper over custom_pbuf structure to keep track of buffer's offset into data region. */
typedef struct pbuf_custom_offset {
    struct pbuf_custom custom;
    uint64_t offset;
} pbuf_custom_offset_t;

typedef struct pbuf_pool {
    union {
        pbuf_custom_offset_t pbuf;
        size_t next_free;
    } *pbufs;
    size_t capacity;
    size_t first_free;
} pbuf_pool_t;

lib_sddf_lwip_config_t lib_config;
lwip_state_t lwip_state;
sddf_state_t sddf_state;
pbuf_pool_t pbuf_pool;

pbuf_pool_t pbuf_pool_init(void *mem, size_t mem_size, size_t pbuf_count)
{
    assert(mem != NULL);
    assert(pbuf_count != 0);
    assert(pbuf_count <= mem_size / sizeof(pbuf_custom_offset_t));

    pbuf_pool_t pool = {
        .pbufs = mem,
        .first_free = 0,
        .capacity = pbuf_count,
    };

    for (size_t i = 0; i < pbuf_count - 1; i++) {
        pool.pbufs[i].next_free = i + 1;
    }
    pool.pbufs[pbuf_count - 1].next_free = SIZE_MAX;

    return pool;
}

pbuf_custom_offset_t *pbuf_pool_alloc(pbuf_pool_t *pool)
{
    assert(pool != NULL);

    if (pool->first_free == SIZE_MAX) {
        return NULL;
    }

    size_t first_free = pool->first_free;
    pool->first_free = pool->pbufs[first_free].next_free;
    return &pool->pbufs[first_free].pbuf;
}

void pbuf_pool_free(pbuf_pool_t *pool, pbuf_custom_offset_t *pbuf)
{
    assert(pool != NULL);
    assert(pbuf != NULL);
    assert((pbuf_custom_offset_t *)pool->pbufs <= pbuf);
    assert(pbuf < (pbuf_custom_offset_t *)&pool->pbufs[pool->capacity]);

    size_t idx = pbuf - (pbuf_custom_offset_t *)pool->pbufs;
    pool->pbufs[idx].next_free = pool->first_free;
    pool->first_free = idx;
}

/**
 * Helper function to convert sddf errors to lwip errors.
 *
 * @param sddf_err sddf error.
 *
 * @return Equivalent lwip error.
 */
static err_t sddf_err_to_lwip_err(net_sddf_err_t sddf_err)
{
    switch (sddf_err) {
    case SDDF_LWIP_ERR_OK:
        return ERR_OK;
    case SDDF_LWIP_ERR_PBUF:
        return ERR_BUF;
    case SDDF_LWIP_ERR_NO_BUF:
        return ERR_MEM;
    case SDDF_LWIP_ERR_ENQUEUED:
        return ERR_OK;
    case SDDF_LWIP_ERR_UNHANDLED:
        return ERR_MEM;
    }
    return ERR_ARG;
}

/**
 * Default netif status callback function. Prints client MAC address and
 * obtained ip address.
 *
 * @param ip_addr Obtained ip address as a string.
 */
static void netif_status_callback_default(char *ip_addr)
{
    uint8_t *mac = lwip_state.netif.hwaddr;
    lwip_state.err_output("LWIP|NOTICE: DHCP request for mac "
                          "%02x:%02x:%02x:%02x:%02x:%02x "
                          "returned ip address: %s\n",
                          mac[0], mac[1], mac[2], mac[3], mac[4], mac[5], ip_addr);
}

/**
 * Default handling function to be called during transmission if tx free
 * queue is empty.
 *
 * @param p pbuf that could not be sent due to queue being empty.
 *
 * @return Simply returns the sddf error indicating nothing was done.
 */
static net_sddf_err_t handle_empty_tx_free_default(struct pbuf *p)
{
    return SDDF_LWIP_ERR_UNHANDLED;
}

/**
 * Returns current time from the timer.
 */
uint32_t sys_now(void)
{
    return sddf_timer_time_now(sddf_state.timer_ch) / NS_IN_MS;
}

void sddf_lwip_process_timeout()
{
    sys_check_timeouts();
}

/**
 * Free a pbuf. This also returns the underlying sddf buffer to the receive free ring.
 *
 * @param p pbuf to free.
 */
static void interface_free_buffer(struct pbuf *p)
{
    SYS_ARCH_DECL_PROTECT(old_level);
    pbuf_custom_offset_t *custom_pbuf_offset = (pbuf_custom_offset_t *)p;
    SYS_ARCH_PROTECT(old_level);
    net_buff_desc_t buffer = { custom_pbuf_offset->offset, 0 };
    int err = net_enqueue_free(&(sddf_state.rx_queue), buffer);
    assert(!err);
    sddf_state.notify_rx = true;
    pbuf_pool_free(&pbuf_pool, custom_pbuf_offset);
    SYS_ARCH_UNPROTECT(old_level);
}

/**
 * Create a pbuf structure to pass to the network interface.
 *
 * @param offset offset into the data region of the buffer to be passed.
 * @param length length of data.
 *
 * @return the newly created pbuf. Can be cast to pbuf_custom.
 */
static struct pbuf *create_interface_buffer(uint64_t offset, size_t length)
{
    pbuf_custom_offset_t *custom_pbuf_offset = (pbuf_custom_offset_t *)pbuf_pool_alloc(&pbuf_pool);
    custom_pbuf_offset->offset = offset;
    custom_pbuf_offset->custom.custom_free_function = interface_free_buffer;

    return pbuf_alloced_custom(PBUF_RAW, length, PBUF_REF, &custom_pbuf_offset->custom,
                               (void *)(offset + sddf_state.rx_buffer_data_region), NET_BUFFER_SIZE);
}

/**
 * Copy a pbuf into an sddf buffer and insert it into the transmit active queue.
 *
 * @param netif lwip network interface state.
 * @param p pbuf to be transmitted.
 *
 * @return If the pbuf is sent, ERR_OK is returned and the pbuf can safely be
 * freed. If the pbuf is too large ERR_MEM is returned. If there are no free
 * sddf buffers available, handle_empty_tx_free will be called with the pbuf,
 * and the equivalent lwip error will be returned.
 */
static err_t lwip_eth_send(struct netif *netif, struct pbuf *p)
{
    if (p->tot_len > NET_BUFFER_SIZE) {
        lwip_state.err_output("LWIP|ERROR: attempted to send a packet of size %u > BUFFER SIZE %u\n", p->tot_len,
                              NET_BUFFER_SIZE);
        return ERR_MEM;
    }

    if (net_queue_empty_free(&sddf_state.tx_queue)) {
        return sddf_err_to_lwip_err(lwip_state.handle_empty_tx_free(p));
    }

    net_buff_desc_t buffer;
    int err = net_dequeue_free(&sddf_state.tx_queue, &buffer);
    assert(!err);

    uintptr_t frame = buffer.io_or_offset + sddf_state.tx_buffer_data_region;
    uint16_t copied = 0;
    for (struct pbuf *curr = p; curr != NULL; curr = curr->next) {
        memcpy((void *)(frame + copied), curr->payload, curr->len);
        copied += curr->len;
    }

    buffer.len = copied;
    err = net_enqueue_active(&sddf_state.tx_queue, buffer);
    assert(!err);

    sddf_state.notify_tx = true;

    return ERR_OK;
}

net_sddf_err_t sddf_lwip_transmit_pbuf(struct pbuf *p)
{
    if (p->tot_len > NET_BUFFER_SIZE) {
        lwip_state.err_output("LWIP|ERROR: attempted to send a packet of size %u > BUFFER SIZE %u\n", p->tot_len,
                              NET_BUFFER_SIZE);
        return SDDF_LWIP_ERR_PBUF;
    }

    if (net_queue_empty_free(&sddf_state.tx_queue)) {
        return lwip_state.handle_empty_tx_free(p);
    }

    err_t err = lwip_eth_send(&lwip_state.netif, p);
    assert(!err);

    return SDDF_LWIP_ERR_OK;
}

void sddf_lwip_process_rx(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!net_queue_empty_active(&sddf_state.rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&sddf_state.rx_queue, &buffer);
            assert(!err);

            struct pbuf *p = create_interface_buffer(buffer.io_or_offset, buffer.len);
            assert(p != NULL);
            if (lwip_state.netif.input(p, &lwip_state.netif) != ERR_OK) {
                lwip_state.err_output("LWIP|ERROR: unknown error inputting pbuf into network stack\n");
                pbuf_free(p);
            }
        }

        net_request_signal_active(&sddf_state.rx_queue);
        reprocess = false;

        if (!net_queue_empty_active(&sddf_state.rx_queue)) {
            net_cancel_signal_active(&sddf_state.rx_queue);
            reprocess = true;
        }
    }
}

/**
 * Initialise the network interface data structure.
 *
 * @param netif network interface data structure.
 */
static err_t ethernet_init(struct netif *netif)
{
    if (netif->state == NULL) {
        return ERR_ARG;
    }

    memcpy(netif->hwaddr, lwip_state.mac, 6);
    netif->mtu = SDDF_LWIP_ETHER_MTU;
    netif->hwaddr_len = ETHARP_HWADDR_LEN;
    netif->output = etharp_output;
    netif->linkoutput = lwip_eth_send;
    netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_LINK_UP | NETIF_FLAG_IGMP;

    return ERR_OK;
}

/**
 * Network interface callback function invoked when DHCP packets are received.
 * If an ip address is successfully obtained, the provided netif_callback
 * function will be invoked with the ip address as a string.
 *
 * @param netif network interface data structure.
 */
static void netif_status_callback(struct netif *netif)
{
    if (dhcp_supplied_address(netif)) {
        char ip4_str[IP4ADDR_STRLEN_MAX];
        lwip_state.netif_callback(ip4addr_ntoa_r(netif_ip4_addr(netif), ip4_str, IP4ADDR_STRLEN_MAX));
    }
}

void sddf_lwip_init(lib_sddf_lwip_config_t *lib_sddf_lwip_config, net_client_config_t *net_config,
                    timer_client_config_t *timer_config, net_queue_handle_t rx_queue, net_queue_handle_t tx_queue,
                    sddf_lwip_err_output_fn err_output, sddf_lwip_netif_status_callback_fn netif_callback,
                    sddf_lwip_handle_empty_tx_free_fn handle_empty_tx_free)
{
    char *magic = (char *)lib_sddf_lwip_config;
    for (int i = 0; i < SDDF_LIB_SDDF_LWIP_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_LIB_SDDF_LWIP_MAGIC[i]) {
            assert(false);
        }
    }
    lib_config = *lib_sddf_lwip_config;

    /* Initialise sddf state */
    sddf_state.rx_queue = rx_queue;
    sddf_state.tx_queue = tx_queue;
    sddf_state.rx_ch = net_config->rx.id;
    sddf_state.tx_ch = net_config->tx.id;
    sddf_state.rx_buffer_data_region = (uintptr_t)net_config->rx_data.vaddr;
    sddf_state.tx_buffer_data_region = (uintptr_t)net_config->tx_data.vaddr;
    sddf_state.timer_ch = timer_config->driver_id;

    /* Initialise lwip state */
    sddf_memcpy(lwip_state.mac, net_config->mac_addr, 6);
    lwip_state.err_output = (err_output == NULL) ? sddf_printf_ : err_output;
    lwip_state.netif_callback = (netif_callback == NULL) ? netif_status_callback_default : netif_callback;
    lwip_state.handle_empty_tx_free = (handle_empty_tx_free == NULL) ? handle_empty_tx_free_default
                                                                     : handle_empty_tx_free;

    lwip_init();

    pbuf_pool = pbuf_pool_init(lib_config.pbuf_pool.vaddr, lib_config.pbuf_pool.size, lib_config.num_pbufs);

    /* Set dummy IP configuration values to get lwIP bootstrapped */
    struct ip4_addr netmask, ipaddr, gw, multicast;
    ipaddr_aton("0.0.0.0", &gw);
    ipaddr_aton("0.0.0.0", &ipaddr);
    ipaddr_aton("0.0.0.0", &multicast);
    ipaddr_aton("255.255.255.0", &netmask);

    lwip_state.netif.name[0] = 'e';
    lwip_state.netif.name[1] = '0';

    if (!netif_add(&(lwip_state.netif), &ipaddr, &netmask, &gw, (void *)&lwip_state, ethernet_init, ethernet_input)) {
        lwip_state.err_output("LWIP|ERROR: Netif add returned NULL\n");
    }

    netif_set_default(&(lwip_state.netif));
    netif_set_status_callback(&(lwip_state.netif), netif_status_callback);
    netif_set_up(&(lwip_state.netif));

    if (dhcp_start(&(lwip_state.netif))) {
        lwip_state.err_output("LWIP|ERROR: failed to start DHCP negotiation\n");
    }
}

void sddf_lwip_maybe_notify()
{
    if (sddf_state.notify_rx && net_require_signal_free(&sddf_state.rx_queue)) {
        net_cancel_signal_free(&sddf_state.rx_queue);
        sddf_state.notify_rx = false;
        sddf_channel curr = sddf_deferred_notify_curr();
        if (curr == -1) {
            sddf_deferred_notify(sddf_state.rx_ch);
        } else if (curr != sddf_state.rx_ch) {
            sddf_notify(sddf_state.rx_ch);
        }
    }

    if (sddf_state.notify_tx && net_require_signal_active(&sddf_state.tx_queue)) {
        net_cancel_signal_active(&sddf_state.tx_queue);
        sddf_state.notify_tx = false;
        sddf_channel curr = sddf_deferred_notify_curr();
        if (curr == -1) {
            sddf_deferred_notify(sddf_state.tx_ch);
        } else if (curr != sddf_state.tx_ch) {
            sddf_notify(sddf_state.tx_ch);
        }
    }
}
