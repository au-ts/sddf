/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <microkit.h>
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

typedef struct lwip_state {
    /* LWIP network interface struct. */
    struct netif netif;
    /* MAC address of client. */
    uint64_t mac;
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
    microkit_channel rx_ch;
    /* sddf channel for net tx virt. */
    microkit_channel tx_ch;
    /* Base address of data region containing rx buffers. */
    uintptr_t rx_buffer_data_region;
    /* Base address of data region containing tx buffers. */
    uintptr_t tx_buffer_data_region;
    /* Boolean indicating whether buffers have been given to rx virt. */
    bool notify_rx;
    /* Boolean indicating whether buffers have been given to tx virt. */
    bool notify_tx;
    /* sddf channel for timer. */
    microkit_channel timer_ch;
} sddf_state_t;

/* Wrapper over custom_pbuf structure to keep track of buffer's offset into data region. */
typedef struct pbuf_custom_offset {
    struct pbuf_custom custom;
    uint64_t offset;
} pbuf_custom_offset_t;

LWIP_MEMPOOL_DECLARE(RX_POOL, SDDF_LWIP_NUM_BUFS * 2, sizeof(struct pbuf_custom_offset), "Zero-copy RX pool");

lwip_state_t lwip_state;
sddf_state_t sddf_state;

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
    case SDDF_ERR_NO_BUF:
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
    LWIP_MEMPOOL_FREE(RX_POOL, custom_pbuf_offset);
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
    pbuf_custom_offset_t *custom_pbuf_offset = (pbuf_custom_offset_t *)LWIP_MEMPOOL_ALLOC(RX_POOL);
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
                lwip_state.err_output("LWIP|ERROR: unkown error inputting pbuf into network stack\n");
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

    net_set_mac_addr(netif->hwaddr, lwip_state.mac);
    netif->mtu = SDDF_LWIP_ETHER_MTU;
    netif->hwaddr_len = ETHARP_HWADDR_LEN;
    netif->output = etharp_output;
    netif->linkoutput = lwip_eth_send;
    NETIF_INIT_SNMP(netif, snmp_ifType_ethernet_csmacd, SDDF_LWIP_LINK_SPEED);
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

void sddf_lwip_init(net_queue_handle_t rx_queue, net_queue_handle_t tx_queue, microkit_channel rx_ch,
                    microkit_channel tx_ch, uintptr_t rx_buffer_data_region, uintptr_t tx_buffer_data_region,
                    microkit_channel timer_ch, uint64_t mac, sddf_lwip_err_output_fn err_output,
                    sddf_lwip_netif_status_callback_fn netif_callback,
                    sddf_lwip_handle_empty_tx_free_fn handle_empty_tx_free)
{
    /* Initialise sddf state */
    sddf_state.rx_queue = rx_queue;
    sddf_state.tx_queue = tx_queue;
    sddf_state.rx_ch = rx_ch;
    sddf_state.tx_ch = tx_ch;
    sddf_state.rx_buffer_data_region = rx_buffer_data_region;
    sddf_state.tx_buffer_data_region = tx_buffer_data_region;
    sddf_state.timer_ch = timer_ch;

    /* Initialise lwip state */
    lwip_state.mac = mac;
    lwip_state.err_output = (err_output == NULL) ? sddf_printf_ : err_output;
    lwip_state.netif_callback = (netif_callback == NULL) ? netif_status_callback_default : netif_callback;
    lwip_state.handle_empty_tx_free = (handle_empty_tx_free == NULL) ? handle_empty_tx_free_default
                                                                     : handle_empty_tx_free;

    lwip_init();

    LWIP_MEMPOOL_INIT(RX_POOL);

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
        if (!microkit_have_signal) {
            microkit_deferred_notify(sddf_state.rx_ch);
        } else if (microkit_signal_cap != BASE_OUTPUT_NOTIFICATION_CAP + sddf_state.rx_ch) {
            microkit_notify(sddf_state.rx_ch);
        }
    }

    if (sddf_state.notify_tx && net_require_signal_active(&sddf_state.tx_queue)) {
        net_cancel_signal_active(&sddf_state.tx_queue);
        sddf_state.notify_tx = false;
        if (!microkit_have_signal) {
            microkit_deferred_notify(sddf_state.tx_ch);
        } else if (microkit_signal_cap != BASE_OUTPUT_NOTIFICATION_CAP + sddf_state.tx_ch) {
            microkit_notify(sddf_state.tx_ch);
        }
    }
}
