#include <os/sddf.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("VIRTIO INPUT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("VIRTIO INPUT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define VIRTIO_ID_NAME_QEMU_KEYBOARD     "QEMU Virtio Keyboard"
#define VIRTIO_ID_NAME_QEMU_MOUSE        "QEMU Virtio Mouse"

#define VIRTIO_INPUT_EVENT_QUEUE 0
#define VIRTIO_INPUT_STATUS_QUEUE 1

#define EVENT_COUNT 256
#define STATUS_COUNT 256

void *virtio_device = (void *)0xa003e00;

volatile virtio_mmio_regs_t *regs;

/* DMA region used for virtIO queues */
uintptr_t virtio_queues_paddr = 0x70000000;
uintptr_t virtio_queues_vaddr = 0x70000000;

// TODO: should actually check that this memory region can fit this many input event buffers
struct virtio_input_event *virtio_event_paddr = (struct virtio_input_event *)0x80000000;
struct virtio_input_event *virtio_event_vaddr = (struct virtio_input_event *)0x80000000;

struct virtq event_virtq;
struct virtq status_virtq;
uint16_t event_last_seen_used = 0;
uint16_t event_last_desc_idx = 0;

/* Allocator for event queue descriptors */
ialloc_t event_ialloc_desc;
uint32_t event_descriptors[EVENT_COUNT];

#define EV_KEY 0x1
#define EV_REL 0x2

#define REL_X 0x0
#define REL_Y 0x1

enum virtio_input_config_select {
    VIRTIO_INPUT_CFG_UNSET      = 0x00,
    VIRTIO_INPUT_CFG_ID_NAME    = 0x01,
    VIRTIO_INPUT_CFG_ID_SERIAL  = 0x02,
    VIRTIO_INPUT_CFG_ID_DEVIDS  = 0x03,
    VIRTIO_INPUT_CFG_PROP_BITS  = 0x10,
    VIRTIO_INPUT_CFG_EV_BITS    = 0x11,
    VIRTIO_INPUT_CFG_ABS_INFO   = 0x12,
};

struct virtio_input_absinfo {
    uint32_t min;
    uint32_t max;
    uint32_t fuzz;
    uint32_t flat;
    uint32_t res;
};

struct virtio_input_devids {
    uint16_t bustype;
    uint16_t vendor;
    uint16_t product;
    uint16_t version;
};

struct virtio_input_config {
    uint8_t select;
    uint8_t subsel;
    uint8_t size;
    uint8_t reserved[5];
    union {
        char string[128];
        uint8_t bitmap[128];
        struct virtio_input_absinfo abs;
        struct virtio_input_devids ids;
    } u;
};

struct virtio_input_event {
    uint16_t type;
    uint16_t code;
    uint32_t value;
};

static void eventq_provide(void);

static void virtio_input_event_print(struct virtio_input_event *event) {
    LOG_DRIVER("event type: 0x%x, code: 0x%x, value: 0x%lx\n", event->type, event->code, event->value);
}

static void virtio_input_config_select(volatile struct virtio_input_config *cfg, uint8_t select, uint8_t subsel) {
    cfg->select = select;
    cfg->subsel = subsel;
}

static inline bool virtio_avail_full_event(struct virtq *virtq)
{
    return event_last_desc_idx >= event_virtq.num;
}

/* Process used buffers put into the event queue by the device. */
static void eventq_process(void) {
    LOG_DRIVER("processing\n");
    uint16_t events_processed = 0;
    uint16_t i = event_last_seen_used;
    uint16_t curr_idx = event_virtq.used->idx;
    while (i != curr_idx) {
        LOG_DRIVER("processing event descriptor %d\n", i);
        struct virtq_used_elem used = event_virtq.used->ring[i % event_virtq.num];
        // Not expecting a chained descriptor at all
        assert(!(event_virtq.desc[used.id].flags & VIRTQ_DESC_F_NEXT));

        struct virtq_desc desc = event_virtq.desc[used.id];

        uintptr_t addr = desc.addr;
        // LOG_DRIVER("addr: 0x%lx, len: %d\n", addr, desc.len);
        assert(desc.len == sizeof(struct virtio_input_event));

        // TODO: clear the virtio_event_vaddr memory after using this descriptor? Probably not worth it
        struct virtio_input_event *event = &virtio_event_vaddr[used.id];
        virtio_input_event_print(event);

        if (event->type == EV_REL) {
            LOG_DRIVER("got EV_REL event\n");
            if (event->code == REL_X) {
                LOG_DRIVER("REL_X\n");
            } else if (event->code == REL_Y) {
                LOG_DRIVER("REL_Y\n");
            }
        } else if (event->type == EV_KEY) {
            LOG_DRIVER("got EV_KEY event\n");
        }

        int err = ialloc_free(&event_ialloc_desc, used.id);
        assert(!err);
        event_last_desc_idx--;
        i++;
        // TODO: I don't know if it's worth having this variable/incrementer
        events_processed++;
    }

    event_last_seen_used += events_processed;

    eventq_provide();
}

/* Populate the eventq with buffers that are at of size struct virtio_input_event so we can actually
 * receive events from the host. */
static void eventq_provide(void) {
    bool transferred = false;
    while (!virtio_avail_full_event(&event_virtq)) {
        // Allocate a desc entry for the packet and the character
        uint32_t event_desc_idx = -1;
        int err = ialloc_alloc(&event_ialloc_desc, &event_desc_idx);
        assert(!err && event_desc_idx != -1);

        assert(event_desc_idx < event_virtq.num);

        event_virtq.desc[event_desc_idx].addr = (uint64_t)&virtio_event_paddr[event_desc_idx];
        event_virtq.desc[event_desc_idx].len = sizeof(struct virtio_input_event);
        event_virtq.desc[event_desc_idx].flags = VIRTQ_DESC_F_WRITE;

        // LOG_DRIVER("adding event %d, 0x%lx\n", event_desc_idx, event_virtq.desc[event_desc_idx].addr);

        // Set the entry in the available ring to point to the descriptor entry fort he packet
        event_virtq.avail->ring[event_virtq.avail->idx % event_virtq.num] = event_desc_idx;
        event_virtq.avail->idx++;
        event_last_desc_idx++;

        transferred = true;
    }

    if (transferred) {
        /* We have added more avail buffers, so notify the device */
        regs->QueueNotify = VIRTIO_INPUT_EVENT_QUEUE;
    }
}

void notified(microkit_channel ch) {
    uint32_t irq_status = regs->InterruptStatus;
    if (irq_status & VIRTIO_MMIO_IRQ_VQUEUE) {
        regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
        eventq_process();
    }

    if (irq_status & VIRTIO_MMIO_IRQ_CONFIG) {
        LOG_DRIVER_ERR("unexpected change in configuration %u\n", irq_status);
    }

    sddf_irq_ack(ch);
}

void input_setup() {
    if (!virtio_mmio_check_magic(regs)) {
        LOG_DRIVER_ERR("invalid virtIO magic value!\n");
        return;
    }

    if (!virtio_mmio_check_device_id(regs, VIRTIO_DEVICE_ID_INPUT)) {
        LOG_DRIVER_ERR("Not a virtIO input device, got ID: %d!\n", regs->DeviceID);
        return;
    }

    if (virtio_mmio_version(regs) != VIRTIO_VERSION) {
        LOG_DRIVER_ERR("not correct virtIO version!\n");
        return;
    }

    LOG_DRIVER("version: 0x%x\n", virtio_mmio_version(regs));

    // Do normal device initialisation (section 3.2)
    // First reset the device
    regs->Status = 0;

    // Set the ACKNOWLEDGE bit to say we have noticed the device
    regs->Status = VIRTIO_DEVICE_STATUS_ACKNOWLEDGE;

    // Set the DRIVER bit to say we know how to drive the device
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER;

    // There are no features to negotiate for an input device
    regs->Status = VIRTIO_DEVICE_STATUS_FEATURES_OK;

    if (!(regs->Status & VIRTIO_DEVICE_STATUS_FEATURES_OK)) {
        LOG_DRIVER_ERR("device status features is not OK!\n");
        return;
    }

    // Setup the virtqueues

    size_t event_desc_off = 0;
    size_t event_avail_off = ALIGN(event_desc_off + (16 * EVENT_COUNT), 2);
    size_t event_used_off = ALIGN(event_avail_off + (6 + 2 * EVENT_COUNT), 4);
    size_t status_desc_off = ALIGN(event_used_off + (6 + 8 * EVENT_COUNT), 16);
    size_t status_avail_off = ALIGN(status_desc_off + (16 * STATUS_COUNT), 2);
    size_t status_used_off = ALIGN(status_avail_off + (6 + 2 * STATUS_COUNT), 4);
    size_t virtq_size = status_used_off + (6 + 8 * STATUS_COUNT);

    event_virtq.num = EVENT_COUNT;
    event_virtq.desc = (struct virtq_desc *)(virtio_queues_paddr + event_desc_off);
    event_virtq.avail = (struct virtq_avail *)(virtio_queues_paddr + event_avail_off);
    event_virtq.used = (struct virtq_used *)(virtio_queues_paddr + event_used_off);

    assert((uintptr_t)event_virtq.desc % 16 == 0);
    assert((uintptr_t)event_virtq.avail % 2 == 0);
    assert((uintptr_t)event_virtq.used % 4 == 0);

    status_virtq.num = STATUS_COUNT;
    status_virtq.desc = (struct virtq_desc *)(virtio_queues_paddr + status_desc_off);
    status_virtq.avail = (struct virtq_avail *)(virtio_queues_paddr + status_avail_off);
    status_virtq.used = (struct virtq_used *)(virtio_queues_paddr + status_used_off);

    assert((uintptr_t)status_virtq.desc % 16 == 0);
    assert((uintptr_t)status_virtq.avail % 2 == 0);
    assert((uintptr_t)status_virtq.used % 4 == 0);

    // Fill up all buffers
    eventq_provide();

    // Setup event queue
    assert(regs->QueueNumMax >= EVENT_COUNT);
    regs->QueueSel = VIRTIO_INPUT_EVENT_QUEUE;
    regs->QueueNum = EVENT_COUNT;
    regs->QueueDescLow = (virtio_queues_paddr + event_desc_off) & 0xFFFFFFFF;
    regs->QueueDescHigh = (virtio_queues_paddr + event_desc_off) >> 32;
    regs->QueueDriverLow = (virtio_queues_paddr + event_avail_off) & 0xFFFFFFFF;
    regs->QueueDriverHigh = (virtio_queues_paddr + event_avail_off) >> 32;
    regs->QueueDeviceLow = (virtio_queues_paddr + event_used_off) & 0xFFFFFFFF;
    regs->QueueDeviceHigh = (virtio_queues_paddr + event_used_off) >> 32;
    regs->QueueReady = 1;

    // Setup status queue
    assert(regs->QueueNumMax >= STATUS_COUNT);
    regs->QueueSel = VIRTIO_INPUT_STATUS_QUEUE;
    regs->QueueNum = STATUS_COUNT;
    regs->QueueDescLow = (virtio_queues_paddr + status_desc_off) & 0xFFFFFFFF;
    regs->QueueDescHigh = (virtio_queues_paddr + status_desc_off) >> 32;
    regs->QueueDriverLow = (virtio_queues_paddr + status_avail_off) & 0xFFFFFFFF;
    regs->QueueDriverHigh = (virtio_queues_paddr + status_avail_off) >> 32;
    regs->QueueDeviceLow = (virtio_queues_paddr + status_used_off) & 0xFFFFFFFF;
    regs->QueueDeviceHigh = (virtio_queues_paddr + status_used_off) >> 32;
    regs->QueueReady = 1;

    // Read from device config

    volatile struct virtio_input_config *virtio_config = (volatile struct virtio_input_config *)regs->Config;

    virtio_input_config_select(virtio_config, VIRTIO_INPUT_CFG_ID_DEVIDS, 0);
    struct virtio_input_devids *devids = &virtio_config->u.ids;
    if (virtio_config->size != 0) {
        LOG_DRIVER("devids bustype: 0x%x, vendor: 0x%x, product: 0x%x, version: 0x%x\n", devids->bustype, devids->vendor, devids->product, devids->version);
    } else {
        LOG_DRIVER("unknown devids\n");
    }

    // Select the event types we want, right now this is hard-coded for QEMU mouse and keyboard.
    virtio_input_config_select(virtio_config, VIRTIO_INPUT_CFG_ID_NAME, 0);
    uint8_t ev_bits;
    if (!memcmp(virtio_config->u.string, VIRTIO_ID_NAME_QEMU_MOUSE, virtio_config->size)) {
        ev_bits = EV_REL;
    } else if (!memcmp(virtio_config->u.string, VIRTIO_ID_NAME_QEMU_KEYBOARD, virtio_config->size)) {
        ev_bits = EV_KEY;
    } else {
        // TODO: strings are not null-terminated, don't do this
        LOG_DRIVER("unknown device: %s\n", virtio_config->u.string);
        assert(false);
    }
    // TODO: strings are not null-terminated, don't do this
    LOG_DRIVER("device: %s\n", virtio_config->u.string);
    virtio_input_config_select(virtio_config, VIRTIO_INPUT_CFG_EV_BITS, ev_bits);
    if (!virtio_config->size) {
        LOG_DRIVER("device did not accept EV bits 0x%x\n", ev_bits);
        assert(false);
    }

    /* Finish initialisation */
    regs->Status |= VIRTIO_DEVICE_STATUS_DRIVER_OK;
}

void init() {
    regs = (volatile virtio_mmio_regs_t *)virtio_device;

    ialloc_init(&event_ialloc_desc, event_descriptors, EVENT_COUNT);

    input_setup();
}
