/*
 * Copyright 2020, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <microkit.h>

#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/udp.h"
#include "lwip/err.h"

#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#include "echo.h"

static struct udp_pcb *udp_socket;

static void lwip_udp_recv_callback(void *arg, struct udp_pcb *pcb, struct pbuf *p, const ip_addr_t *addr, u16_t port)
{
    err_t error = udp_sendto(pcb, p, addr, port);
    if (error) sddf_dprintf("Failed to send UDP packet through socket: %s\n", lwip_strerr(error));
    pbuf_free(p);
}

int setup_udp_socket(void)
{
    udp_socket = udp_new_ip_type(IPADDR_TYPE_V4);
    if (udp_socket == NULL) {
        sddf_dprintf("Failed to open a UDP socket\n");
        return -1;
    }

    int error = udp_bind(udp_socket, IP_ANY_TYPE, UDP_ECHO_PORT);
    if (error == ERR_OK) {
        udp_recv(udp_socket, lwip_udp_recv_callback, udp_socket);
    } else {
        sddf_dprintf("Failed to bind the UDP socket\n");
        return -1;
    }

    return 0;
}