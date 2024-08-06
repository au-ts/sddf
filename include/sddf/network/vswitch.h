#pragma once
#include <microkit.h>
#include <sddf/network/queue.h>

#define VSWITCH_MAX_PORT_COUNT 64

typedef uint64_t vswitch_port_bitmap_t;

typedef struct vswitch_channel {
    net_queue_handle_t q;
    microkit_channel ch;
    char *data_region;
} vswitch_channel_t;

/* These ports are analogous to ports on a physical switch.
 * They represent a medium you can send to and receive from. */
typedef struct vswitch_port {
    /* For clients, incoming is TX, outgoing is RX.
     * For virtualisers, incoming is RX, outgoing is TX. */ 
    vswitch_channel_t incoming;
    vswitch_channel_t outgoing;
    vswitch_port_bitmap_t allow_list;
} vswitch_port_t;

static inline bool vswitch_can_send_to(vswitch_port_t *src, int dst)
{
    return src->allow_list & (1 << (uint64_t)dst);
}
