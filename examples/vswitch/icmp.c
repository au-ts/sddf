#include "icmp.h"
#include <sddf/network/lib_sddf_lwip.h>
#include <sddf/network/config.h>
#include "lwip/raw.h"
#include "lwip/icmp.h"
#include "lwip/inet_chksum.h"
#include "lwip/prot/ip4.h"
#include "lwip/prot/ip.h"

static struct raw_pcb *ping_pcb;
static icmp_context_t *contexts[SDDF_NET_MAX_CLIENTS];

#define PING_ID_BASE        0xA100
#define PING_DEBUG     LWIP_DBG_ON

static inline uint8_t ping_id_to_client_id(uint16_t ping_id)
{
    return (uint8_t)(ping_id - PING_ID_BASE);
}

static inline uint16_t client_id_to_ping_id(uint8_t client_id)
{
    return (uint16_t)(client_id + PING_ID_BASE);
}

/**
 * Prepare the ICMP echo packet.
 *
 * @param iecho pointer to the ICMP echo header to fill in
 * @param len length of the header
 * @param seq_num pointer to the sequence number to increment and then pass in the header
 * @param client_id ID of the client who is will be sending the packet
 */
static void ping_prepare_echo(struct icmp_echo_hdr *iecho, uint16_t len, uint16_t *seq_num, uint8_t client_id)
{
    size_t i;
    size_t data_len = len - sizeof(struct icmp_echo_hdr);

    ICMPH_TYPE_SET(iecho, ICMP_ECHO);
    ICMPH_CODE_SET(iecho, 0);
    iecho->chksum = 0;
    iecho->id     = lwip_htons(client_id_to_ping_id(client_id));
    iecho->seqno  = lwip_htons(++(*seq_num));

    /* fill the additional data buffer with some data */
    for (i = 0; i < data_len; i++) {
        ((char*)iecho)[sizeof(struct icmp_echo_hdr) + i] = (char)i;
    }

    iecho->chksum = inet_chksum(iecho, len);
}

/**
 * ICMP receive callback. Called by the raw API when the packet is of ICMP type.
 *
 * @param arg Optional user passed argument
 * @param pcb the raw_pcb which received data
 * @param p the packet buffer that was received
 * @param addr the remote IP address from which the packet was received
 * @return 1 if the packet was 'eaten' (aka. deleted),
 *         0 if the packet lives on
 */
static uint8_t ping_recv(void *arg, struct raw_pcb *pcb, struct pbuf *p, const ip_addr_t *addr)
{
    icmp_context_t **contexts = (icmp_context_t **)arg;
    const struct ip_hdr *iphdr;
    const struct icmp_echo_hdr *iecho;
    uint16_t ip_hlen;
    uint16_t ping_id_host;
    uint8_t client_id;

    LWIP_UNUSED_ARG(pcb);
    LWIP_ASSERT("addr != NULL", addr != NULL);
    LWIP_ASSERT("p != NULL", p != NULL);

    //sddf_printf("ICMP LOG: Received the ICMP from %s len=%u\n",
    //            ipaddr_ntoa(addr), p->tot_len);

    if (p->tot_len < sizeof(struct ip_hdr) + sizeof(struct icmp_echo_hdr)) {
        return 0;
    }

    iphdr = (const struct ip_hdr *)p->payload;
    ip_hlen = (uint16_t)(IPH_HL(iphdr) * 4);

    if (p->tot_len < ip_hlen + sizeof(struct icmp_echo_hdr)) {
        return 0;
    }

    iecho = (const struct icmp_echo_hdr *)((const uint8_t *)p->payload + ip_hlen);
    /* Only replies count as success */
    if (ICMPH_TYPE(iecho) != ICMP_ER) {
        return 0;
    }

    ping_id_host = lwip_ntohs(iecho->id);
    if (ping_id_host < PING_ID_BASE ||
        ping_id_host >= PING_ID_BASE + SDDF_NET_MAX_CLIENTS) {
        return 0;
    }

    client_id = ping_id_to_client_id(ping_id_host);

    if (contexts[client_id] == NULL) {
        return 0;
    }

    if (lwip_ntohs(iecho->seqno) != contexts[client_id]->seq_num) {
        return 0;
    }

    sddf_printf("ICMP reply matched on netif %s peer=%u seq=%u from %s\n",
                 sddf_get_pd_name(), client_id, contexts[client_id]->seq_num, ipaddr_ntoa(addr));

    contexts[client_id]->reply_received = true; // TODO: what to do with this knowledge?

    return 0;
}

/**
 * ICMP raw API initialization function. Binds the ICMP contexts to the receive callback.
 */
void icmp_init_raw()
{
    ping_pcb = raw_new(IP_PROTO_ICMP);
    LWIP_ASSERT("ping_pcb != NULL", ping_pcb != NULL);

    raw_recv(ping_pcb, ping_recv, contexts);
    raw_bind(ping_pcb, IP_ADDR_ANY);
}

/**
 * Sends a single ICMP echo packet to a client using LWiPs raw API.
 *
 * @param ctx ICMP context per ping session
 * @param client_id client's ID that will be pinged
 * @return informs whether the sending was successful
 */
bool send_icmp_request(icmp_context_t *ctx, uint8_t client_id)
{
    err_t err = ERR_OK;
    struct pbuf *p;
    struct icmp_echo_hdr *iecho;
    size_t ping_size = sizeof(struct icmp_echo_hdr) + PING_DATA_SIZE;
    ip_addr_t addr;
    ip_addr_set_ip4_u32(&addr, ctx->ip_addr);
    contexts[client_id] = ctx;
    //ipaddr_aton("172.16.0.2", &addr); // TODO: this is for testing purposes - can see it in wireshark

    sddf_printf("ICMP dst = %s raw=0x%08x\n", ipaddr_ntoa(&addr), ctx->ip_addr);
    p = pbuf_alloc(PBUF_IP, (u16_t)ping_size, PBUF_RAM);
    if (!p) {
        return false;
    }
    if ((p->len == p->tot_len) && (p->next == NULL)) {
        iecho = (struct icmp_echo_hdr *)p->payload;

        ping_prepare_echo(iecho, (u16_t)ping_size, &ctx->seq_num, client_id);

        err = raw_sendto(ping_pcb, p, &addr);
        sddf_lwip_maybe_notify();

        sddf_printf("Sent the ICMP for netif %s success: %d\n", sddf_get_pd_name(), err == ERR_OK);
    }
    pbuf_free(p);
    return err == ERR_OK;
}
