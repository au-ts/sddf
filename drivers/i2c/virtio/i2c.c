#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/ialloc.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>
#include <sddf/util/printf.h>
#include <sddf/util/fence.h>
#include "virtio_i2c.h"

/* Channels */
#define VIRTUALISER_CH 0
#define IRQ_CH 1

#define REQUEST_COUNT 512
#define HW_RING_SIZE (0x10000)

volatile virtio_mmio_regs_t *regs = 0;
uintptr_t i2c_regs;
uintptr_t virtio_mmio_i2c_offset = 0;

uintptr_t virtio_requestq_vaddr;
uintptr_t virtio_requestq_paddr;
uintptr_t virtio_i2c_in_hdr_vaddr;
uintptr_t virtio_i2c_in_hdr_paddr;
uintptr_t virtio_i2c_req_buf_vaddr;
uintptr_t virtio_i2c_req_buf_paddr;
uintptr_t virtio_i2c_out_hdr_vaddr;
uintptr_t virtio_i2c_out_hdr_paddr;

ialloc_t req_ialloc_desc;
/* Multply request count by 3 for the out_hdr, buf, in_hdr. */
uint64_t req_descriptors[REQUEST_COUNT * 3];

struct virtq requestq;
uint16_t rq_last_seen_used = 0;

i2c_queue_handle_t i2c_queue;
uintptr_t request_region;
uintptr_t response_region;
uintptr_t driver_data_region;

virtio_i2c_state_t state;

int rq_last_desc_idx = 0;
#define ALIGN(x, align)   (((x) + (align) - 1) & ~((align) - 1))

static inline bool virtio_avail_full_rq() {
    return rq_last_desc_idx >= requestq.num;
}

void handle_request(void)
{
    if (!i2c_queue_empty(i2c_queue.request)) {

        size_t bus_address = 0;
        size_t offset = 0;
        unsigned int size = 0;
        int err = i2c_dequeue_request(i2c_queue, &bus_address, &offset, &size);
        sddf_dprintf("this is the value of size: %d\n", size);
        if (err) {
            LOG_DRIVER_ERR("fatal: failed to dequeue request\n");
            return;
        }

        i2c_token_t *data = (i2c_token_t *) driver_data_region + offset;
        state.curr_data = driver_data_region + offset;
        uint16_t curr_flags = 0;

        size_t out_hdr_desc;
        err = ialloc_alloc(&req_ialloc_desc, &out_hdr_desc);
        assert(!err);
        assert(out_hdr_desc < requestq.num);
        size_t in_hdr_desc;
        err = ialloc_alloc(&req_ialloc_desc, &in_hdr_desc);
        assert(!err);
        assert(in_hdr_desc < requestq.num);
        /* Don't allocate this til we actually have a data segment. */
        size_t req_buf_desc;

        struct virtio_i2c_out_hdr *out_hdr = virtio_i2c_out_hdr_vaddr + (out_hdr_desc * sizeof(struct virtio_i2c_out_hdr));
        struct virtio_i2c_in_hdr *in_hdr = virtio_i2c_in_hdr_vaddr + (in_hdr_desc * sizeof(struct virtio_i2c_in_hdr));
        out_hdr->addr = (uint16_t) bus_address;
        out_hdr->padding = 0;
        out_hdr->flags = 0;
        in_hdr->status = 0;
        /* Connect the in and out headers here. If we have a data token, allocate and insert a data buffer
        in between these two descriptors. This is to support zero length messages. */

        /* We will place at out header desc index. */
        requestq.desc[out_hdr_desc].addr = virtio_i2c_out_hdr_paddr + (out_hdr_desc * (sizeof(struct virtio_i2c_out_hdr)));
        requestq.desc[out_hdr_desc].len = sizeof(struct virtio_i2c_out_hdr);
        /* Check if the VIRTIO_I2C_FLAGS_M_RD has been set and set the R/W for the desc appropriately. */
        requestq.desc[out_hdr_desc].flags = VIRTQ_DESC_F_NEXT;
        requestq.desc[out_hdr_desc].next = in_hdr_desc;
        requestq.desc[in_hdr_desc].addr = virtio_i2c_in_hdr_paddr + (in_hdr_desc * sizeof(struct virtio_i2c_in_hdr));
        requestq.desc[in_hdr_desc].len = sizeof(struct virtio_i2c_in_hdr);
        requestq.desc[in_hdr_desc].flags = VIRTQ_DESC_F_WRITE;

        requestq.avail->ring[requestq.avail->idx % requestq.num] = out_hdr_desc;

        /* Keep track of if we have inserted a data segment in the descriptor chain. */
        uint8_t *buf = NULL;
        uint32_t buf_flags = 0;

        bool is_read = false;
        /* Scan through the token list and enqueue into the virtqueues */
        for (int i = 0; i < size; i++) {
            /* We want to chain reads and writes. We will send an empty buffer with fail next cleared
            when we recv an end token. */
            if (data[i] == I2C_TOKEN_ADDR_READ) {
                sddf_dprintf("This is a read request\n");
                is_read = true;
                out_hdr->flags = VIRTIO_I2C_FLAGS_M_RD;
            } else if (data[i] == I2C_TOKEN_ADDR_WRITE) {
                sddf_dprintf("This is a write request\n");
                out_hdr->flags = 0;
                is_read = false;
            } else if (data[i] == I2C_TOKEN_END) {
                curr_flags = 0;
                buf_flags = VIRTQ_DESC_F_WRITE;
            } else if (data[i] == I2C_TOKEN_DATA) {
                sddf_dprintf("Found data token\n");
                if (buf == NULL) {
                    err = ialloc_alloc(&req_ialloc_desc, &req_buf_desc);
                    assert(!err);
                    assert(req_buf_desc < requestq.num);

                    /* This is not the most efficient way to allocate memory for the
                    req buffer, but is the simplest to book keep for. */
                    buf = virtio_i2c_req_buf_vaddr + (req_buf_desc * (sizeof(uint8_t) * I2C_MAX_DATA_SIZE));
                    /* Insert buffer into desc chain. */
                    requestq.desc[req_buf_desc].addr = virtio_i2c_req_buf_paddr + (req_buf_desc * (sizeof(uint8_t) * I2C_MAX_DATA_SIZE));
                    requestq.desc[req_buf_desc].next = requestq.desc[out_hdr_desc].next;
                    requestq.desc[out_hdr_desc].next = req_buf_desc;
                    requestq.desc[req_buf_desc].flags = VIRTQ_DESC_F_NEXT | buf_flags;
                    requestq.desc[req_buf_desc].len = 0;
                }
                if (is_read == false) {
                    /* Data is layed out directly after this DATA_TOKEN */
                    i++;
                    assert(i < size);
                    buf[requestq.desc[req_buf_desc].len] = data[i];
                    requestq.desc[req_buf_desc].len++;
                } else if (is_read) {
                    buf[requestq.desc[req_buf_desc].len] = 0;
                   requestq.desc[req_buf_desc].len++;
                }

            }
        }
        sddf_dprintf("This was the size of the req buffer: %d\n", requestq.desc[req_buf_desc].len);
        requestq.avail->idx++;
        rq_last_desc_idx += 1;
    } else {
        LOG_DRIVER("called but no work available: resetting notified flag\n");
    }
}

void handle_irq() {
    if (regs->InterruptStatus & (1 << 1)) {
        LOG_DRIVER_ERR("VIRT-I2C| Got erroneous config IRQ!\n");
        regs->InterruptACK = (1 << 1);
    } else if (regs->InterruptStatus & (1 << 0)) {
        /* Dequeue from the used queue. */
        size_t i = rq_last_seen_used;
        size_t curr_idx = requestq.used->idx;
        while (i != curr_idx) {
            struct virtio_i2c_out_hdr *i2c_out_hdr = NULL;
            uint8_t *buf = NULL;
            struct virtio_i2c_in_hdr *i2c_in_hdr = NULL;

            struct virtq_used_elem out_hdr_elem = requestq.used->ring[i % requestq.num];
            struct virtq_desc out_hdr = requestq.desc[out_hdr_elem.id];
            i2c_out_hdr = virtio_i2c_out_hdr_vaddr + (out_hdr_elem.id * sizeof(struct virtio_i2c_out_hdr));

            /* Get the next. This could be a buf or an in_hdr. */
            struct virtq_desc in_hdr = requestq.desc[out_hdr.next % requestq.num];
            struct virtq_desc buf_hdr;
            int err = ialloc_free(&req_ialloc_desc, out_hdr_elem.id);
            assert(!err);
            err = ialloc_free(&req_ialloc_desc, out_hdr.next);
            assert(!err);
            rq_last_desc_idx -= 2;
            if (in_hdr.flags | VIRTQ_DESC_F_NEXT) {
                /* Then this one is the actual in header */
                buf_hdr = in_hdr;
                in_hdr = requestq.desc[buf_hdr.next % requestq.num];
                err = ialloc_free(&req_ialloc_desc, buf_hdr.next);
                assert(!err);
                rq_last_desc_idx -= 1;
                sddf_dprintf("This used elem has a buffer!\n");
                buf = virtio_i2c_req_buf_vaddr + (out_hdr.next * (sizeof(uint8_t) * I2C_MAX_DATA_SIZE));
                i2c_in_hdr = virtio_i2c_in_hdr_vaddr + (buf_hdr.next * sizeof(struct virtio_i2c_out_hdr));
            } else {
                i2c_in_hdr = virtio_i2c_in_hdr_vaddr + (out_hdr.next * sizeof(struct virtio_i2c_out_hdr));
            }

            uint8_t *ret_buf = state.curr_data;

            /* Check if this was a read. */
            if (i2c_out_hdr->flags == VIRTIO_I2C_FLAGS_M_RD) {
                /* If its a read, we must return the buffer.
                If it was a write, we are done processing. */

                if (i2c_in_hdr->status == VIRTIO_I2C_MSG_ERR) {
                    LOG_DRIVER_ERR("VIRT-I2C| There was an error reading from the device!\n");
                    ret_buf[RESPONSE_ERR] = I2C_ERR_NOREAD;
                    /* @krishnan: Not sure what to put for current token here, as we only
                    have an error for the entire request. */
                    ret_buf[RESPONSE_ERR_TOKEN] = 0x0;
                } else {
                    /* For now using length that we requested from the device */
                    for (int i = 0; i < buf_hdr.len; i++) {
                        size_t index = RESPONSE_DATA_OFFSET + state.len;
                        ret_buf[index] = buf[i];
                        sddf_dprintf("This is the data we read from the device: %b\n", buf[i]);
                        state.len++;
                    }
                }
            }
            ret_buf[RESPONSE_ERR] = I2C_ERR_OK;
            ret_buf[RESPONSE_ERR_TOKEN] = 0x0;
            sddf_dprintf("This is the len in the response: %d\n", state.len);
            int ret = i2c_enqueue_response(i2c_queue, i2c_out_hdr->addr, state.curr_data - driver_data_region, state.len + RESPONSE_DATA_OFFSET);
            state.curr_data = 0;
            state.len = 0;
            i++;
        }

        regs->InterruptACK = (1 << 0);
        rq_last_seen_used = curr_idx;
        microkit_notify(VIRTUALISER_CH);
        /* @krishnan: The meson driver resets the device here, do we need to do something similar? */
    }

    return;
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

    sddf_dprintf("These are the device features: %b\n", features);

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

    ialloc_init(&req_ialloc_desc, req_descriptors, REQUEST_COUNT * 3);

    i2c_queue = i2c_queue_init(request_region, response_region);

    /* Setup the virtqueue. This is all we need to initialize for the i2c adapter
    according to the virtio-i2c spec. */

    size_t rq_desc_off = 0;
    size_t rq_avail_off = rq_desc_off + (16 * REQUEST_COUNT);
    size_t rq_used_off = rq_avail_off + (6 + 2 * REQUEST_COUNT);
    size_t size = rq_used_off + (6 + 8 * REQUEST_COUNT);

    assert(size <= HW_RING_SIZE);

    /* Align the physical addresses. We can calculate the offset to use for our
    virtual addresses from these. */
    uintptr_t phys_descq = ALIGN((virtio_requestq_paddr + rq_desc_off),16);
    uintptr_t phys_drivq = ALIGN((virtio_requestq_paddr + rq_avail_off),2);
    uintptr_t phys_devq = ALIGN((virtio_requestq_paddr + rq_used_off),4);

    /* We want our request count to be *3 */
    requestq.num = REQUEST_COUNT;
    requestq.desc = (struct virtq_desc *)(virtio_requestq_vaddr + (phys_descq - virtio_requestq_paddr));
    requestq.avail = (struct virtq_avail *)(virtio_requestq_vaddr + (phys_drivq - virtio_requestq_paddr));
    requestq.used = (struct virtq_used *)(virtio_requestq_vaddr + (phys_devq - virtio_requestq_paddr));

    /* Select the first queue. We only need 1 for i2c. */
    regs->QueueSel = 0;
    assert(regs->QueueNumMax >= REQUEST_COUNT);
    regs->QueueNum = REQUEST_COUNT;
    regs->QueueDescLow = phys_descq & 0xFFFFFFFF;
    regs->QueueDescHigh = phys_descq >> 32;
    regs->QueueDriverLow = phys_drivq & 0xFFFFFFFF;
    regs->QueueDriverHigh = phys_drivq >> 32;
    regs->QueueDeviceLow = phys_devq & 0xFFFFFFFF;
    regs->QueueDeviceHigh = phys_devq >> 32;
    THREAD_MEMORY_RELEASE();

    regs->QueueReady = 1;

    sddf_dprintf("Finished initialising the virtq for i2c requests!\n");

    // rq_provide();
    /* Set Driver OK status bit */
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER_OK;
    sddf_dprintf("We have finished intialisation for virtio i2c driver\n");
    state.curr_data = 0;
    state.len = 0;
}

void notified(microkit_channel ch)
{
    switch (ch) {
        case VIRTUALISER_CH:
            sddf_dprintf("Attempting to handle request\n");
            handle_request();
            regs->QueueNotify = 0;
            break;
        case IRQ_CH:
            handle_irq();
            microkit_irq_ack(ch);
            break;
        default:
            microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
}