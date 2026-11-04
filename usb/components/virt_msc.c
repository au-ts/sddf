/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/usb/constants.h>
#include <sddf/usb/device.h>
#include <sddf/util/printf.h>

/* Uncomment this to enable debug logging */
// #define DEBUG_MSC_VIRT

#if defined(DEBUG_MSC_VIRT)
#define LOG_MSC_VIRT(...) do{ sddf_dprintf("MSC_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_MSC_VIRT(...) do{}while(0)
#endif
#define LOG_MSC_VIRT_ERR(...) do{ sddf_dprintf("MSC_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

static const msc_device_t *msc = (msc_device_t *) MSC_DEVICE_VADDR;

void init(void)
{
    (void) msc;
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    bool success = false;

    uint64_t label = seL4_MessageInfo_get_label(msginfo);
    switch (label) {
        case CLIENT_MSC_INQUIRY: {
            LOG_MSC_VIRT("Client requested MSC inquiry\n");
            seL4_MessageInfo_t msg = seL4_MessageInfo_new(MSC_VIRT_INQUIRY, 0, 0, 0);
            msg = sddf_ppcall(USB_PROTOCOL_STACK, msg);
            success = seL4_MessageInfo_get_label(msg);
            if (success) {
                LOG_MSC_VIRT("MSC inquiry succeeded\n");
                LOG_MSC_VIRT("    %.8s %.16s rev %.4s\n",
                             msc->inquiry_resp.vendor_id,
                             msc->inquiry_resp.product_id,
                             msc->inquiry_resp.product_rev);
            } else {
                LOG_MSC_VIRT_ERR("MSC inquiry failed\n");
            }
            break;
        }
        default: {
            LOG_MSC_VIRT_ERR("Received unexpected PPC with label %lu\n", label);
            break;
        }
    }

    return seL4_MessageInfo_new(success, 0, 0, 0);
}

void notified(sddf_channel ch)
{
    switch (ch) {
        case VIRT_MSC_MOUNT: {
            LOG_MSC_VIRT("A mass storage device has been mounted\n");
            sddf_notify(CLIENT_MSC_MOUNT);
            break;
        }
        case VIRT_MSC_UNMOUNT: {
            LOG_MSC_VIRT("A mass storage device has been unmounted\n");
            sddf_notify(CLIENT_MSC_UNMOUNT);
            break;
        }
        default: {
            LOG_MSC_VIRT_ERR("Received unexpected notification from Channel "
                             "%u\n", ch);
            break;
        }
    }
}
