#include "icmp.h"
#include <sddf/network/lib_sddf_lwip.h>
#include "lwip/raw.h"
#include "lwip/icmp.h"
#include "lwip/inet_chksum.h"
#include "lwip/prot/ip4.h"
#include "lwip/prot/ip.h"

static struct raw_pcb *ping_pcb;
static uint16_t ping_seq_num; // TODO: for now single seq num - but need to have multiple...

// TODO: should be unique?
#define PING_ID        0xAFAF
#define PING_DEBUG     LWIP_DBG_ON

static void
ping_prepare_echo(struct icmp_echo_hdr *iecho, uint16_t len, uint16_t *seq_num)
{
    size_t i;
    size_t data_len = len - sizeof(struct icmp_echo_hdr);

    ICMPH_TYPE_SET(iecho, ICMP_ECHO);
    ICMPH_CODE_SET(iecho, 0);
    iecho->chksum = 0;
    iecho->id     = PING_ID;
    iecho->seqno  = lwip_htons(++(*seq_num));

    /* fill the additional data buffer with some data */
    for (i = 0; i < data_len; i++) {
        ((char*)iecho)[sizeof(struct icmp_echo_hdr) + i] = (char)i;
    }

    iecho->chksum = inet_chksum(iecho, len);
}

static u8_t
ping_recv(void *arg, struct raw_pcb *pcb, struct pbuf *p, const ip_addr_t *addr)
{
  struct icmp_echo_hdr *iecho;
  LWIP_UNUSED_ARG(arg);
  LWIP_UNUSED_ARG(pcb);
  LWIP_UNUSED_ARG(addr);
  LWIP_ASSERT("addr != NULL", addr != NULL);
  LWIP_ASSERT("p != NULL", p != NULL);

    sddf_printf("ICMP LOG: Received the ICMP\n");
  if ((p->tot_len >= (IP_HLEN + sizeof(struct icmp_echo_hdr))) &&
      pbuf_remove_header(p, IP_HLEN) == 0) {
    iecho = (struct icmp_echo_hdr *)p->payload;

    if ((iecho->id == PING_ID) && (iecho->seqno == lwip_htons(ping_seq_num))) {
      LWIP_DEBUGF( PING_DEBUG, ("ping: recv "));
      ip_addr_debug_print(PING_DEBUG, addr);
      //LWIP_DEBUGF( PING_DEBUG, (" %"U32_F" ms\n", (sys_now()-ping_time)));

      /* do some ping result processing */
      //PING_RESULT(1);
      // TODO: do something
      pbuf_free(p);
      return 1; /* eat the packet */
    }
    /* not eaten, restore original packet */
    pbuf_add_header(p, IP_HLEN);
  }

  return 0; /* don't eat the packet */
}

void icmp_init_raw()
{
    ping_pcb = raw_new(IP_PROTO_ICMP);
    LWIP_ASSERT("ping_pcb != NULL", ping_pcb != NULL);

    raw_recv(ping_pcb, ping_recv, NULL);
    raw_bind(ping_pcb, IP_ADDR_ANY);
}

bool send_icmp_request(icmp_context_t *ctx)
{
    err_t err;
    struct pbuf *p;
    struct icmp_echo_hdr *iecho;
    size_t ping_size = sizeof(struct icmp_echo_hdr) + PING_DATA_SIZE;
    ip_addr_t addr;
    ip_addr_set_ip4_u32(&addr, lwip_htonl(ctx->ip_addr));
    //ipaddr_aton("172.16.0.2", &addr); // TODO: this is for testing purposes - can see it in wireshark

    sddf_printf("call the ICMP request\n");
    p = pbuf_alloc(PBUF_IP, (u16_t)ping_size, PBUF_RAM);
    if (!p) {
        return false;
    }
    if ((p->len == p->tot_len) && (p->next == NULL)) {
        iecho = (struct icmp_echo_hdr *)p->payload;

        ping_prepare_echo(iecho, (u16_t)ping_size, &ping_seq_num); // TODO: should be seq from ctx

        sddf_printf("Sending the ICMP\n");
        err = raw_sendto(ping_pcb, p, &addr);
        sddf_lwip_maybe_notify();
        sddf_printf("Sent the ICMP success: %d\n", err == ERR_OK);
    }
    pbuf_free(p);
    return err == ERR_OK;
}
