#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/ialloc.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>
#include "virtio_i2c.h"

volatile virtio_mmio_regs_t *regs;
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

struct virtq requestq;

uintptr_t i2c_regs;

#define VIRTIO_MMIO_I2C_OFFSET (0xc00)
#define REQUEST_COUNT 512
#define HW_RING_SIZE (0x10000)

void init(void)
{
    regs = (volatile virtio_mmio_regs_t *) (i2c_regs + VIRTIO_MMIO_I2C_OFFSET);

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

    sddf_dprintf("These are features low: %b --- these are features high: %b\n", feature_low, feature_high);

    /* According to the virtio i2c spec we must negotiate the following features:
     * VIRTIO_I2C_F_ZERO_LENGTH_REQUEST
     */

    // Check that the feature is offered by the device
    if (!(features & ((uint64_t)1 << VIRTIO_I2C_F_ZERO_LENGTH_REQUEST))) {
        LOG_DRIVER_ERR("Device does not offer zero length request. Unable to negotiate!\n");
        regs->Status = VIRTIO_DEVICE_STATUS_FAILED;
        return;
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

    // Set Driver OK status bit
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER_OK;
}

void notified(microkit_channel ch)
{

}