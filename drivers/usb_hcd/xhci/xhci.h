#include <stdint.h>

/*
 * TinyUSB functions -> should go in wider include
 */

/*
 * xHCI regs and data
 */

#define XHCI_MAX_DEVICE_SLOTS 64

struct xhci_cap_regs {
    uint8_t caplength;
    uint8_t rsvd;
    uint16_t hciversion;
    uint32_t hcsparams1;
    union {
        uint32_t raw;
        struct {
            uint32_t ist            : 4;
            uint32_t erst_max       : 4;
            uint32_t rsvd0          : 13;
            uint32_t max_sp_buf_hi  : 5;
            uint32_t spr            : 1;
            uint32_t max_sp_buf_lo  : 5;
        } structured;
    } hcsparams2;
    uint32_t hcsparams3;
    uint32_t hccparams1;
    uint32_t dboff;
    uint32_t rtsoff;
    uint32_t hccparams2;
};
_Static_assert(sizeof(struct xhci_cap_regs) == 0x20, "bad xhci_cap_regs struct");

struct xhci_port_regs {
    uint32_t portsc;
    uint32_t portpmsc;
    uint32_t portli;
    uint32_t porthlpmc;
};
_Static_assert(sizeof(struct xhci_port_regs) == 0x10, "bad xhci_port_regs struct");

struct xhci_op_regs {
    union {
        uint32_t raw;
        struct {
            uint32_t rs         : 1;
            uint32_t hcrst      : 1;
            uint32_t inte       : 1;
            uint32_t hsee       : 1;
            uint32_t css        : 1;
            uint32_t crs        : 1;
            uint32_t ewe        : 1;
            uint32_t eu3s       : 1;
            uint32_t rsvd1      : 1;
            uint32_t cme        : 1;
            uint32_t ete        : 1;
            uint32_t etc_tsc    : 1;
            uint32_t vtio       : 1;
            uint32_t rsvd0      : 16;
        } structured;
    } usb_cmd;
    union {
        uint32_t raw;
        struct {
            uint32_t hch        : 1;
            uint32_t rsvd2      : 1;
            uint32_t hse        : 1;
            uint32_t eint       : 1;
            uint32_t pcd        : 1;
            uint32_t rsvd1      : 3;
            uint32_t sss        : 1;
            uint32_t rss        : 1;
            uint32_t sre        : 1;
            uint32_t cnr        : 1;
            uint32_t hce        : 1;
            uint32_t rsvd0      : 19;
        } structured;
    } usb_sts;
    uint32_t pagesize;
    uint32_t rsvd0[2];
    uint32_t dnctrl;
    uint32_t crcr;
    uint32_t rsvd1[4];
    uint64_t dcbaap;
    union {
        uint32_t raw;
        struct {
            uint32_t max_slots_en   : 8;
            uint32_t u3e            : 1;
            uint32_t cie            : 1;
            uint32_t rsvd0          : 22;
        } structured;
    } config;
    uint32_t rsvd2[241];
    struct xhci_port_regs ports[XHCI_MAX_DEVICE_SLOTS];
};
_Static_assert(sizeof(struct xhci_op_regs) == 0x800, "bad xhci_op_regs struct");

struct xhci_interrupter_regs {
    uint32_t iman;
    uint32_t imod;
    uint32_t erstsz;
    uint32_t rsvd0;
    uint64_t erstba;
    uint64_t erdp;
};
_Static_assert(sizeof(struct xhci_interrupter_regs) == 0x20, "bad xhci_interrupter_regs struct");

struct xhci_runtime_regs {
    uint32_t mfindex;
    uint32_t rsvd0[7];
    struct xhci_interrupter_regs interrupters[1024];
};
_Static_assert(sizeof(struct xhci_runtime_regs) == 0x8020, "bad xhci_runtime_regs struct");

struct xhci_doorbell_regs {
    union {
        uint32_t raw;
        struct {
            uint32_t db_target      : 8;
            uint32_t rsvd0          : 8;
            uint32_t db_stream_id   : 16;
        } structured;
    } db[256];
};
_Static_assert(sizeof(struct xhci_doorbell_regs) == 0x400, "bad xhci_doorbell_regs struct");

struct xhci_slot_context {
    union {
        uint32_t raw;
        struct {
            uint32_t route_string   : 20;
            uint32_t rsvd0          : 5;
            uint32_t mtt            : 1;
            uint32_t hub            : 1;
            uint32_t context_entries: 5;
        } structured;
    } field0;
    union {
        uint32_t raw;
        struct {
            uint32_t max_exit_latency   : 16;
            uint32_t root_hub_port_num  : 8;
            uint32_t num_ports          : 8;
        } structured;
    } field1;
    union {
        uint32_t raw;
        struct {
            uint32_t parent_hub_slot_id : 8;
            uint32_t parent_port_num    : 8;
            uint32_t ttt                : 1;
            uint32_t rsvd               : 4;
            uint32_t interrupter_target : 11;
        } structured;
    } field2;
    union {
        uint32_t raw;
        struct {
            uint32_t usb_device_addr    : 8;
            uint32_t rsvd0              : 19;
            uint32_t slot_state         : 5;
        } structured;
    } field3;
    uint32_t rsvd0[4];
};
_Static_assert(sizeof(struct xhci_slot_context) == 0x20, "bad struct xhci_slot_context");


struct xhci_endpoint_context {
    union {
        uint32_t raw;
        struct {
            uint32_t endpoint_state     : 3;
            uint32_t rsvd0              : 5;
            uint32_t mult               : 2;
            uint32_t max_primary_streams: 5;
            uint32_t lsa                : 1;
            uint32_t interval           : 8;
            uint32_t max_esit_payload_hi: 8;
        } structured;
    } field0;
    union {
        uint32_t raw;
        struct {
            uint32_t rsvd0          : 1;
            uint32_t error_count    : 2;
            uint32_t endpoint_type  : 3;
            uint32_t rsvd1          : 1;
            uint32_t hinit_disable  : 1;
            uint32_t max_burst_size : 8;
            uint32_t max_packet_size: 16;
        } structured;
    } field1;
    union {
        uint64_t raw;
        struct {
            uint32_t dcs            : 1;
            uint32_t rvd0           : 3;
            uint64_t tr_dequeue_ptr : 60;
        } structured;
    } field2;
    union {
        uint32_t raw;
        struct {
            uint32_t avg_trb_len            : 16;
            uint32_t max_esit_payload_lo    : 16;
        } structured;
    } field3;
    uint32_t rsvd0[3];
};
_Static_assert(sizeof(struct xhci_endpoint_context) == 0x20, "bad struct xhci_slot_context");

struct xhci_device_context {
    struct xhci_slot_context slot_context;
    struct xhci_endpoint_context endpoint_contexts[31];
};
_Static_assert(sizeof(struct xhci_device_context) == 0x400, "bad struct xhci_device_context");

struct xhci_device_context_base_address_array {
    void *scratchpads;
    struct xhci_device_context *device_contexts[];
};