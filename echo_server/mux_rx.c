#include "shared_ringbuffer.h"
#include "util.h"
#include "netif/ethernet.h"

uintptr_t rx_free_drv;
uintptr_t rx_used_drv;

uintptr_t rx_free_cli;
uintptr_t rx_used_cli;

uintptr_t shared_dma_vaddr;
uintptr_t shared_dma_paddr;
uintptr_t uart_base;

#define NUM_CLIENTS 1
#define DMA_SIZE 0x200000
#define COPY_CH 0
#define DRIVER_CH 1

#define ETHER_MTU 1500

typedef struct state {
    /* Pointers to shared buffers */
    ring_handle_t rx_ring_drv;
    ring_handle_t rx_ring_clients[NUM_CLIENTS];
    uint8_t mac_addrs[NUM_CLIENTS][6];
} state_t;

state_t state;
int initialised = 0;
uint8_t broadcast[6] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
uint64_t dropped = 0;
bool rx_free_was_empty = false;

static uintptr_t
get_phys_addr(uintptr_t virtual)
{
    uint64_t offset = -1;
    if (virtual >= shared_dma_vaddr && virtual < shared_dma_vaddr + DMA_SIZE) {
        offset = virtual - shared_dma_vaddr;
    }

    if (offset < 0) {
        print("get_phys_addr: offset < 0");
        return 0;
    }

    return shared_dma_paddr + offset;
}

static uintptr_t
get_virt_addr(uintptr_t phys)
{
    uint64_t offset = -1;
    if (phys >= shared_dma_paddr && phys < shared_dma_paddr + DMA_SIZE) {
        offset = phys - shared_dma_paddr;
    }

    if (offset < 0 || offset >= DMA_SIZE) {
        print("get_phys_addr: offset < 0 || offset >= dma size");
        return 0;
    }

    return shared_dma_vaddr + offset;
}

static void
dump_mac(uint8_t *mac)
{
    for (unsigned i = 0; i < 6; i++) {
        sel4cp_dbg_putc(hexchar((mac[i] >> 4) & 0xf));
        sel4cp_dbg_putc(hexchar(mac[i] & 0xf));
        if (i < 5) {
            sel4cp_dbg_putc(':');
        }
    }
    sel4cp_dbg_putc('\n');
}

int compare_mac(uint8_t *mac1, uint8_t *mac2)
{
    for (int i = 0; i < 6; i++) {
        if (mac1[i] != mac2[i]) {
            return -1;
        }
    }
    return 0;
}

/* Return the client ID if the Mac address is a match. */
int get_client(uintptr_t dma_vaddr) {
    uint8_t dest_addr[6];
    struct eth_hdr *ethhdr = (struct eth_hdr *)dma_vaddr;
    dest_addr[0] = ethhdr->dest.addr[0];
    dest_addr[1] = ethhdr->dest.addr[1];
    dest_addr[2] = ethhdr->dest.addr[2];
    dest_addr[3] = ethhdr->dest.addr[3];
    dest_addr[4] = ethhdr->dest.addr[4];
    dest_addr[5] = ethhdr->dest.addr[5];

    for (int client = 0; client < NUM_CLIENTS; client++) {
        if (compare_mac(dest_addr, state.mac_addrs[client]) == 0) {
            return client;
        }
        if (compare_mac(dest_addr, broadcast) == 0) {
            // broadcast packet, send the packet to the first client to handle.
            // This is temporary, eventually we will have a different
            // component to deal with this.
            return 0;
        }
    }
    return -1;
}

/*
 * Loop over driver and insert all used rx buffers to appropriate client queues.
 */
void process_rx_complete(void)
{
    int notify_clients[NUM_CLIENTS] = {0};

    /* To avoid notifying the driver twice, used this global variable to 
        determine whether we need to notify the driver in 
        process_rx_free() as we dropped some packets */
    dropped = 0;
    rx_free_was_empty = ring_empty(state.rx_ring_drv.free_ring);

    while (!ring_empty(state.rx_ring_drv.used_ring)) {
        uintptr_t addr = 0;
        unsigned int len = 0;
        void *cookie = NULL;

        int err = dequeue_used(&state.rx_ring_drv, &addr, &len, &cookie);
        assert(!err);

        int vaddr = get_virt_addr(addr);
        if (!vaddr) {
            print("MUX RX|ERROR: get_virt_addr returned 0\nPhys: ");
            puthex64(addr);
            print("\n");
        }

        err = seL4_ARM_VSpace_Invalidate_Data(3, vaddr, vaddr + ETHER_MTU);
        if (err) {
            print("MUX RX|ERROR: ARM Vspace invalidate failed\n");
            puthex64(err);
            print("\n");
        }

        // Get MAC address and work out which client it is.
        int client = get_client(vaddr);
        if (client >= 0 && !ring_full(state.rx_ring_clients[client].used_ring)) {
            /* enqueue it. */
            int was_empty = ring_empty(state.rx_ring_clients[client].used_ring);
            int err = enqueue_used(&state.rx_ring_clients[client], vaddr, len, cookie);
            assert(!err);
            if (err) {
                print("MUX RX|ERROR: failed to enqueue onto used ring\n");
            }

            if (was_empty) {
                notify_clients[client] = 1;
            }
        } else {
            // no match, not for us, return the buffer to the driver.
            if (addr == 0) {
                print("MUX RX|ERROR: Attempting to add NULL buffer to driver RX ring\n");
                break;
            }
            err = enqueue_free(&state.rx_ring_drv, addr, len, cookie);
            if (err) {
                print("MUX RX|ERROR: Failed to enqueue free to driver RX ring\n");
            }
            dropped++;
        }
    }

    /* Loop over bitmap and see who we need to notify. */
    for (int client = 0; client < NUM_CLIENTS; client++) {
        if (notify_clients[client]) {
            sel4cp_notify(client);
        }
    }
}

// Loop over all client rings and return unused rx buffers to the driver
bool process_rx_free(void)
{
    /* If we have enqueued to the driver's free ring and the free
     * ring was empty, we want to notify the driver. We also only want to
     * notify it only once.
     */
    uint64_t original_size = ring_size(state.rx_ring_drv.free_ring);
    uint64_t enqueued = 0;
    for (int i = 0; i < NUM_CLIENTS; i++) {
        while (!ring_empty(state.rx_ring_clients[i].free_ring)) {
            uintptr_t addr;
            unsigned int len;
            void *buffer;
            int err = dequeue_free(&state.rx_ring_clients[i], &addr, &len, &buffer);
            assert(!err);

            int paddr = get_phys_addr(addr);
            if (!paddr) {
                print("MUX RX|ERROR: get_phys_addr returned 0\nvirt: ");
                puthex64(addr);
                print("\n");
            }
            err = enqueue_free(&state.rx_ring_drv, paddr, len, buffer);
            assert(!err);
            enqueued += 1;
        }
    }

    /* We only want to notify the driver if the queue either was empty, or
       it wasn't empty, but the driver interrupted us above and emptied it, 
       and thus the number of packets we enqueued does not equal the ring_size now 
       (So the driver could have missed an empty to full ntfn)
       
       We also could have enqueued packets into the free ring during 
       process_rx_complete(), so we could have also missed this empty condition.
       */
    if (((original_size == 0 || 
            original_size + enqueued != ring_size(state.rx_ring_drv.free_ring))
            && enqueued != 0) ||
            (dropped != 0 && rx_free_was_empty)) {
        sel4cp_notify_delayed(DRIVER_CH);
    }

    return enqueued;
}

seL4_MessageInfo_t
protected(sel4cp_channel ch, sel4cp_msginfo msginfo)
{
    if (ch >= NUM_CLIENTS) {
        sel4cp_dbg_puts("Received ppc on unexpected channel ");
        puthex64(ch);
        return sel4cp_msginfo_new(0, 0);
    }
    // return the MAC address.
    uint32_t lower = (state.mac_addrs[ch][0] << 24) |
                     (state.mac_addrs[ch][1] << 16) |
                     (state.mac_addrs[ch][2] << 8) |
                     (state.mac_addrs[ch][3]);
    uint32_t upper = (state.mac_addrs[ch][4] << 24) | (state.mac_addrs[ch][5] << 16);
    sel4cp_dbg_puts("Mux rx is sending mac: ");
    dump_mac(state.mac_addrs[ch]);
    sel4cp_mr_set(0, lower);
    sel4cp_mr_set(1, upper);
    return sel4cp_msginfo_new(0, 2);
}

void notified(sel4cp_channel ch)
{
    if (!initialised) {
        process_rx_free();
        sel4cp_notify(DRIVER_CH);
        initialised = 1;
        return;
    }

    if (ch == COPY_CH || ch == DRIVER_CH) {
        process_rx_complete();
        process_rx_free();
    } else {
        print("MUX RX|ERROR: unexpected notification from channel: ");
        puthex64(ch);
        print("\n");
        assert(0);
    }
}

void init(void)
{
    // set up client macs
    // use a dummy one for our one client. 
    state.mac_addrs[0][0] = 0x52;
    state.mac_addrs[0][1] = 0x54;
    state.mac_addrs[0][2] = 0x1;
    state.mac_addrs[0][3] = 0;
    state.mac_addrs[0][4] = 0;
    state.mac_addrs[0][5] = 0;

    // This is the legitimate hw address
    // (can be useful when debugging). 
    /*state.mac_addrs[0][0] = 0;
    state.mac_addrs[0][1] = 0x4;
    state.mac_addrs[0][2] = 0x9f;
    state.mac_addrs[0][3] = 0x5;
    state.mac_addrs[0][4] = 0xf8;
    state.mac_addrs[0][5] = 0xcc;*/

    /* Set up shared memory regions */
    ring_init(&state.rx_ring_drv, (ring_buffer_t *)rx_free_drv, (ring_buffer_t *)rx_used_drv, NULL, 1);

    // FIX ME: Use the notify function pointer to put the notification in?
    ring_init(&state.rx_ring_clients[0], (ring_buffer_t *)rx_free_cli, (ring_buffer_t *)rx_used_cli, NULL, 0);

    return;
}

