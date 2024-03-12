#include <string.h>
#include <microkit.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/network/constants.h>
#include <sddf/network/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define RX_CH 0
#define TX_CH 1
#define CLIENT_CH 2
#define REG_IP 0
#define IPV4_PROTO_LEN 4
#define PADDING_SIZE 10
#define LWIP_IANA_HWTYPE_ETHERNET 1
#define NUM_ARP_CLIENTS (NUM_CLIENTS - 1)

ring_handle_t rx_ring;
ring_handle_t tx_ring;

uintptr_t rx_free;
uintptr_t rx_used;
uintptr_t tx_free;
uintptr_t tx_used;

uintptr_t rx_buffer_data_region;
uintptr_t tx_buffer_data_region;

uintptr_t uart_base;

uint8_t mac_addrs[NUM_ARP_CLIENTS][ETH_HWADDR_LEN];
uint32_t ipv4_addrs[NUM_ARP_CLIENTS];

struct __attribute__((__packed__)) arp_packet {
    uint8_t ethdst_addr[ETH_HWADDR_LEN];
    uint8_t ethsrc_addr[ETH_HWADDR_LEN];
    uint16_t type;
    uint16_t hwtype;
    uint16_t proto;
    uint8_t hwlen;
    uint8_t protolen;
    uint16_t opcode;
    uint8_t hwsrc_addr[ETH_HWADDR_LEN];
    uint32_t ipsrc_addr;
    uint8_t hwdst_addr[ETH_HWADDR_LEN];
    uint32_t ipdst_addr;
    uint8_t padding[10];
    uint32_t crc;
};

static char *ipaddr_to_string(uint32_t s_addr, char *buf, int buflen)
{
    char inv[3], *rp;
    uint8_t *ap, rem, n, i;
    int len = 0;

    rp = buf;
    ap = (uint8_t *)&s_addr;
    for (n = 0; n < 4; n++) {
        i = 0;
        do {
            rem = *ap % (uint8_t)10;
            *ap /= (uint8_t)10;
            inv[i++] = (char)('0' + rem);
        } while (*ap);
        while (i--) {
            if (len++ >= buflen) return NULL;
            *rp++ = inv[i];
        }
        if (len++ >= buflen) return NULL;
        *rp++ = '.';
        ap++;
    }
    *--rp = 0;
    return buf;
}

static int match_ip_to_client(uint32_t addr)
{
    for (int i = 0; i < NUM_ARP_CLIENTS; i++) {
        if (ipv4_addrs[i] == addr) {
            return i;
        }
    }

    return -1;
}

static int arp_reply(const uint8_t ethsrc_addr[ETH_HWADDR_LEN],
                const uint8_t ethdst_addr[ETH_HWADDR_LEN],
                const uint8_t hwsrc_addr[ETH_HWADDR_LEN], const uint32_t ipsrc_addr,
                const uint8_t hwdst_addr[ETH_HWADDR_LEN], const uint32_t ipdst_addr)
{
    if (ring_empty(tx_ring.free_ring)) {
        dprintf("ARP|LOG: Transmit free ring empty or transmit used ring full. Dropping reply\n");
        return -1;
    }

    buff_desc_t buffer;
    int err __attribute__((unused)) = dequeue_free(&tx_ring, &buffer);
    assert(!err);

    uintptr_t addr = tx_buffer_data_region + buffer.phys_or_offset;

    struct arp_packet *reply = (struct arp_packet *)addr;
    memcpy(&reply->ethdst_addr, ethdst_addr, ETH_HWADDR_LEN);
    memcpy(&reply->ethsrc_addr, ethsrc_addr, ETH_HWADDR_LEN);

    reply->type = HTONS(ETH_TYPE_ARP);
    reply->hwtype = HTONS(LWIP_IANA_HWTYPE_ETHERNET);
    reply->proto = HTONS(ETH_TYPE_IP);
    reply->hwlen = ETH_HWADDR_LEN;
    reply->protolen = IPV4_PROTO_LEN;
    reply->opcode = HTONS(ETHARP_OPCODE_REPLY);

    memcpy(&reply->hwsrc_addr, hwsrc_addr, ETH_HWADDR_LEN);
    reply->ipsrc_addr = ipsrc_addr;
    memcpy(&reply->hwdst_addr, hwdst_addr, ETH_HWADDR_LEN); 
    reply->ipdst_addr = ipdst_addr;
    memset(&reply->padding, 0, 10);

    buffer.len = 56;
    err = enqueue_used(&tx_ring, buffer);
    assert(!err);

    return 0;
}

void receive(void)
{
    bool transmitted = false;
    bool reprocess = true;
    while (reprocess) {
        while (!ring_empty(rx_ring.used_ring)) {
            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_used(&rx_ring, &buffer);
            assert(!err);
            uintptr_t addr = rx_buffer_data_region + buffer.phys_or_offset;

            /* Check if packet is an ARP request */
            struct ethernet_header *ethhdr = (struct ethernet_header *)addr;
            if (ethhdr->type == HTONS(ETH_TYPE_ARP)) {
                struct arp_packet *pkt = (struct arp_packet *)addr;
                /* Check if it's a probe, ignore announcements */
                if (pkt->opcode == HTONS(ETHARP_OPCODE_REQUEST)) {
                    /* Check it it's for a client */
                    int client = match_ip_to_client(pkt->ipdst_addr);
                    if (client >= 0) {
                        /* Send a response */
                        if (!arp_reply(mac_addrs[client], pkt->ethsrc_addr, mac_addrs[client], pkt->ipdst_addr,
                                    pkt->hwsrc_addr, pkt->ipsrc_addr)) transmitted = true;
                    }
                }
            }

            buffer.len = 0;
            err = enqueue_free(&rx_ring, buffer);
            assert(!err);
        }

        request_signal(rx_ring.used_ring);
        reprocess = false;

        if (!ring_empty(rx_ring.used_ring)) {
            cancel_signal(rx_ring.used_ring);
            reprocess = true;
        }
    }

    if (transmitted && require_signal(tx_ring.used_ring)) {
        cancel_signal(tx_ring.used_ring);
        microkit_notify_delayed(TX_CH);
    }
}

void notified(microkit_channel ch)
{
    receive();
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    int client = ch - CLIENT_CH;
    if (client >= NUM_ARP_CLIENTS || client < 0) {
        dprintf("ARP|LOG: PPC from unkown client %d\n", client);
        return microkit_msginfo_new(0, 0);
    }

    uint32_t ip_addr = microkit_mr_get(0);
    uint32_t mac_higher = microkit_mr_get(1);
    uint32_t mac_lower = microkit_mr_get(2);
    uint64_t mac = (((uint64_t) mac_higher) << 32) | mac_lower;

    char buf[16];
    switch (microkit_msginfo_get_label(msginfo)) {
        case REG_IP:
            printf("ARP|NOTICE: client%d registering ip address: %s with MAC: %02x:%02x:%02x:%02x:%02x:%02x\n", 
                        client, ipaddr_to_string(ip_addr, buf, 16), mac >> 40, mac >> 32 & 0xff, mac >> 24 & 0xff, 
                        mac >> 16 & 0xff, mac >> 8 & 0xff, mac & 0xff);
            ipv4_addrs[client] = ip_addr;
            break;
        default:
            dprintf("ARP|LOG: PPC from client%d with unknown message label %llu\n", client, microkit_msginfo_get_label(msginfo));
            break;
    }

    return microkit_msginfo_new(0, 0);
}

void init(void)
{
    ring_init(&rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, RX_RING_SIZE_ARP);
    ring_init(&tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, TX_RING_SIZE_ARP);
    buffers_init((ring_buffer_t *)tx_free, 0, TX_RING_SIZE_ARP);

    arp_mac_addr_init_sys(microkit_name, (uint8_t *) mac_addrs);
}