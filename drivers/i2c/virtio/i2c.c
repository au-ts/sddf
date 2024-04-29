#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/ialloc.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>
#include <sddf/util/printf.h>
#include "virtio_i2c.h"

volatile virtio_mmio_regs_t *regs;
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

struct virtq requestq;

uintptr_t virtio_i2c_headers_vaddr;
uintptr_t virtio_i2c_headers_paddr;

uintptr_t i2c_regs;

uintptr_t virtio_mmio_i2c_offset = 0;

/* Channels */
#define VIRTUALISER_CH 0
#define IRQ_CH 1

#define REQUEST_COUNT 512
#define HW_RING_SIZE (0x10000)

static inline void handle_request(void)
{
    LOG_DRIVER("handling request\n");
    volatile struct i2c_regs *regs = (volatile struct i2c_regs *) i2c_regs;
    if (!i2c_queue_empty(queue_handle.request)) {
        // If this interface is busy, skip notification and
        // set notified flag for later processing
        if (i2c_ifState.curr_request_data) {
            microkit_dbg_puts("driver: request in progress, deferring notification\n");
            i2c_ifState.notified = 1;
            return;
        }
        // microkit_dbg_puts("driver: starting work for bus\n");
        // Otherwise, begin work. Start by extracting the request

        size_t bus_address = 0;
        size_t offset = 0;
        unsigned int size = 0;
        int err = i2c_dequeue_request(queue_handle, &bus_address, &offset, &size);
        if (err) {
            LOG_DRIVER_ERR("fatal: failed to dequeue request\n");
            return;
        }

        // Load bookkeeping data into return buffer
        // Set client PD

        LOG_DRIVER("Loading request from client %u to address 0x%x of sz %zu\n", req[0], req[1], size);

        if (size > I2C_MAX_DATA_SIZE) {
            LOG_DRIVER_ERR("Invalid request size: %u!\n", size);
            return;
        }
        i2c_ifState.curr_request_data = (i2c_token_t *) DATA_REGIONS_START + offset;
        i2c_ifState.addr = bus_address;
        i2c_ifState.curr_request_len = size;
        i2c_ifState.remaining = size;    // Ignore client PD and address
        i2c_ifState.notified = 0;

        // Trigger work start
        // @ivanv: check return value
        i2c_load_tokens(regs);
    } else {
        LOG_DRIVER("called but no work available: resetting notified flag\n");
        // If nothing needs to be done, clear notified flag if it was set.
        i2c_ifState.notified = 0;
    }
}

void init(void)
{

    /*
    *   Rudementry device discovery. Map in all the virtio-mmio regions and scan
    *   them for an i2c device.
    *
    *   NOTE: This offset changes depending on how many virtio-mmio devices
    *   there are in the system.
    *
    *   You will also have to manually update the IRQ number in the system description
    *   file. Use the offset printed here, and reference with the dts output by QEMU
    *   to find the corresponding IRQ number.
    */

    for (int i = 0; i < 0x3f00; i+= 0x200) {
        regs = (volatile virtio_mmio_regs_t *) (i2c_regs + i);
        if (virtio_mmio_check_device_id(regs, VIRTIO_DEVICE_ID_I2C)) {
            sddf_dprintf("This is a virtio i2c device at offset: %p\n", i);
            virtio_mmio_i2c_offset = i;
        }
    }

    regs = (volatile virtio_mmio_regs_t *) (i2c_regs + virtio_mmio_i2c_offset);

    // Do MMIO device init (section 4.2.3.1)
    if (!virtio_mmio_check_magic(regs)) {
        LOG_DRIVER_ERR("invalid virtIO magic value!\n");
        return;
    }

    if (virtio_mmio_version(regs) != VIRTIO_VERSION) {
        LOG_DRIVER_ERR("not correct virtIO version!\n");
        return;
    }

    if (!virtio_mmio_check_device_id(regs, VIRTIO_DEVICE_ID_I2C)) {
        LOG_DRIVER_ERR("not a virtIO i2c device!\n");
        return;
    }

    sddf_dprintf("Checks pass! Valid I2C device!\n");

    // Device initialisation (section 3.1)

    // Writing 0 to status reg causes device reset
    regs->Status = 0;

    // Set Acknowledge status bit
    regs->Status = VIRTIO_DEVICE_STATUS_ACKNOWLEDGE;

    // Set Driver status bit
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER;

    // Read the device feature bits
    regs->DeviceFeaturesSel = 0;
    uint32_t feature_low = regs->DeviceFeatures;
    regs->DeviceFeaturesSel = 1;
    uint32_t feature_high = regs->DeviceFeatures;
    uint64_t features = feature_low | ((uint64_t)feature_high << 32);

    /* According to the virtio i2c spec we must negotiate the following features:
     * VIRTIO_I2C_F_ZERO_LENGTH_REQUEST
     */

    // Check that the feature is offered by the device
    if (!(feature_low & ((uint64_t)1 << VIRTIO_I2C_F_ZERO_LENGTH_REQUEST))) {
        LOG_DRIVER_ERR("Device does not offer zero length request. Unable to negotiate!\n");
        regs->Status = VIRTIO_DEVICE_STATUS_FAILED;
        return;
    } else {
        sddf_dprintf("Device offers zero length request, negotiating features.\n");
    }

    regs->DriverFeaturesSel = 0;
    regs->DriverFeatures = (uint64_t)1 << VIRTIO_I2C_F_ZERO_LENGTH_REQUEST;
    regs->DriverFeaturesSel = 1;
    regs->DriverFeatures = 0;

    // Set the Features OK status bit
    regs->Status = VIRTIO_DEVICE_STATUS_FEATURES_OK;

    if (!(regs->Status & VIRTIO_DEVICE_STATUS_FEATURES_OK)) {
        LOG_DRIVER_ERR("device status features is not OK!\n");
        regs->Status = VIRTIO_DEVICE_STATUS_FAILED;
        return;
    }

    // Setup the virtq. This is all we need to initialize for i2c.

    // @kwinter double check these offsets
    size_t rq_desc_off = 0;
    size_t rq_avail_off = rq_desc_off + (16 * REQUEST_COUNT);
    size_t rq_used_off = rq_avail_off + (6 + 2 * REQUEST_COUNT);
    size_t size = rq_used_off + (6 + 8 * REQUEST_COUNT);

    assert(size <= HW_RING_SIZE);

    requestq.num = REQUEST_COUNT;
    requestq.desc = (struct virtq_desc *)(hw_ring_buffer_vaddr + rq_desc_off);
    requestq.avail = (struct virtq_avail *)(hw_ring_buffer_vaddr + rq_avail_off);
    requestq.used = (struct virtq_used *)(hw_ring_buffer_vaddr + rq_used_off);

    assert(regs->QueueNumMax >= REQUEST_COUNT);
    /* Select the first queue. We only need 1 for i2c. */
    regs->QueueSel = 0;
    regs->QueueNum = REQUEST_COUNT;
    regs->QueueDescLow = (hw_ring_buffer_paddr + rq_desc_off) & 0xFFFFFFFF;
    regs->QueueDescHigh = (hw_ring_buffer_paddr + rq_desc_off) >> 32;
    regs->QueueDriverLow = (hw_ring_buffer_paddr + rq_avail_off) & 0xFFFFFFFF;
    regs->QueueDriverHigh = (hw_ring_buffer_paddr + rq_avail_off) >> 32;
    regs->QueueDeviceLow = (hw_ring_buffer_paddr + rq_used_off) & 0xFFFFFFFF;
    regs->QueueDeviceHigh = (hw_ring_buffer_paddr + rq_used_off) >> 32;
    regs->QueueReady = 1;

    // Set Driver OK status bit
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER_OK;
}

void notified(microkit_channel ch)
{
    switch (ch) {
        case VIRTUALISER_CH:
            handle_request();
            break;
        case IRQ_CH:
            handle_irq(false);
            microkit_irq_ack(ch);
            break;
        default:
            microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
}