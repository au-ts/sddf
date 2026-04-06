#include <stdint.h>

/*
 * TinyUSB functions -> should go in wider include
 */

/*
 * xHCI regs and data
 */
struct xhci_cap_regs {
    uint8_t caplength;
    uint8_t rsvd;
    uint16_t hciversion;
    uint32_t hcsparams1;
    uint32_t hcsparams2;
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
            uint32_t rsvd0      : 16;
            uint32_t vtio       : 1;
            uint32_t etc_tsc    : 1;
            uint32_t ete        : 1;
            uint32_t cme        : 1;
            uint32_t rsvd1      : 1;
            uint32_t eu3s       : 1;
            uint32_t ewe        : 1;
            uint32_t crs        : 1;
            uint32_t css        : 1;
            uint32_t lhcrst     : 1;
            uint32_t hsee       : 1;
            uint32_t inte       : 1;
            uint32_t hcrst      : 1;
            uint32_t rs         : 1;
        } structured;
    } usb_cmd;
    union {
        uint32_t raw;
        struct {
            uint32_t rsvd0      : 19;
            uint32_t hce        : 1;
            uint32_t cnr        : 1;
            uint32_t sre        : 1;
            uint32_t rss        : 1;
            uint32_t sss        : 1;
            uint32_t rsvd1      : 3;
            uint32_t pcd        : 1;
            uint32_t eint       : 1;
            uint32_t hse        : 1;
            uint32_t rsvd2      : 1;
            uint32_t hch        : 1;
        } structured;
    } usb_sts;
    uint32_t pagesize;
    uint32_t rsvd0[2];
    uint32_t dnctrl;
    uint32_t crcr;
    uint32_t rsvd1[4];
    uint64_t dcbaap;
    uint32_t config;
    uint32_t rsvd2[241];
    struct xhci_port_regs ports[64]; /* hardcoded=64, configured as such in xhci.c */
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
            uint32_t db_stream_id   : 16;
            uint32_t rsvd0          : 8;
            uint32_t db_target      : 8;
        } structured;
    } db[256];
};
_Static_assert(sizeof(struct xhci_doorbell_regs) == 0x400, "bad xhci_doorbell_regs struct");