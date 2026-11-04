/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/usb/constants.h>
#include <sddf/util/printf.h>
#include <host/usbh.h>

bool hcd_configure(uint8_t rhport, uint32_t cfg_id, const void *cfg_param)
{
    (void) cfg_param;
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_CONFIGURE, 0, 0, 2);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(CFG_ID, cfg_id);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

bool hcd_init(uint8_t rhport, const tusb_rhport_init_t *rh_init)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_INIT, 0, 0, 3);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(RH_ROLE, rh_init->role);
    sddf_set_mr(RH_SPEED, rh_init->speed);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

void hcd_int_handler(uint8_t rhport, bool in_isr)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_INT_HANDLER, 0, 0, 2);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(IN_ISR, in_isr);
    sddf_ppcall(USB_DRIVER, msg);
}

void hcd_int_enable(uint8_t rhport)
{
    (void) rhport;
}

void hcd_int_disable(uint8_t rhport)
{
    (void) rhport;
}

uint32_t hcd_frame_number(uint8_t rhport)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_FRAME_NUMBER, 0, 0, 1);
    sddf_set_mr(RHPORT, rhport);
    sddf_ppcall(USB_DRIVER, msg);
    return sddf_get_mr(FRAME_NUMBER);
}

bool hcd_port_connect_status(uint8_t rhport)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_PORT_CONNECT_STATUS, 0, 0, 1);
    sddf_set_mr(RHPORT, rhport);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

void hcd_port_reset(uint8_t rhport)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_PORT_RESET, 0, 0, 1);
    sddf_set_mr(RHPORT, rhport);
    sddf_ppcall(USB_DRIVER, msg);
}

void hcd_port_reset_end(uint8_t rhport)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_PORT_RESET_END, 0, 0, 1);
    sddf_set_mr(RHPORT, rhport);
    sddf_ppcall(USB_DRIVER, msg);
}

tusb_speed_t hcd_port_speed_get(uint8_t rhport)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_PORT_SPEED_GET, 0, 0, 1);
    sddf_set_mr(RHPORT, rhport);
    sddf_ppcall(USB_DRIVER, msg);
    return sddf_get_mr(PORT_SPEED);
}

void hcd_device_close(uint8_t rhport, uint8_t dev_addr)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_DEVICE_CLOSE, 0, 0, 2);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(DEV_ADDR, dev_addr);
    sddf_ppcall(USB_DRIVER, msg);
}

bool hcd_edpt_open(uint8_t rhport, uint8_t dev_addr,
                   tusb_desc_endpoint_t const *ep_desc)
{
    uint32_t hi = 0;
    uint32_t lo = 0;
    memcpy(&hi, (void *) ep_desc, sizeof(hi));
    memcpy(&lo, (void *) ep_desc + sizeof(hi), sizeof(lo));

    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_EDPT_OPEN, 0, 0, 4);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(DEV_ADDR, dev_addr);
    sddf_set_mr(EP_DESC_HI, hi);
    sddf_set_mr(EP_DESC_LO, lo);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

bool hcd_edpt_close(uint8_t rhport, uint8_t daddr, uint8_t ep_addr)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_EDPT_CLOSE, 0, 0, 3);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(DEV_ADDR, daddr);
    sddf_set_mr(EP_ADDR, ep_addr);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

bool hcd_edpt_xfer(uint8_t rhport, uint8_t dev_addr, uint8_t ep_addr,
                   uint8_t *buffer, uint16_t buflen)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_EDPT_XFER, 0, 0, 4);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(DEST, (dev_addr << CHAR_BIT) | ep_addr);
    sddf_set_mr(BUFFER, (uintptr_t) buffer);
    sddf_set_mr(BUFLEN, buflen);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

bool hcd_edpt_abort_xfer(uint8_t rhport, uint8_t dev_addr, uint8_t ep_addr)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_EDPT_ABORT_XFER, 0, 0, 3);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(DEV_ADDR, dev_addr);
    sddf_set_mr(EP_ADDR, ep_addr);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

bool hcd_setup_send(uint8_t rhport, uint8_t dev_addr,
                    uint8_t const setup_packet[8])
{
    uint32_t hi = 0;
    uint32_t lo = 0;
    memcpy(&hi, (void *) setup_packet, sizeof(hi));
    memcpy(&lo, (void *) setup_packet + sizeof(hi), sizeof(lo));

    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_SETUP_SEND, 0, 0, 4);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(DEV_ADDR, dev_addr);
    sddf_set_mr(SETUP_HI, hi);
    sddf_set_mr(SETUP_LO, lo);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}

bool hcd_edpt_clear_stall(uint8_t rhport, uint8_t dev_addr, uint8_t ep_addr)
{
    seL4_MessageInfo_t msg = seL4_MessageInfo_new(HCD_EDPT_CLEAR_STALL, 0, 0, 3);
    sddf_set_mr(RHPORT, rhport);
    sddf_set_mr(DEV_ADDR, dev_addr);
    sddf_set_mr(EP_ADDR, ep_addr);
    msg = sddf_ppcall(USB_DRIVER, msg);
    return seL4_MessageInfo_get_label(msg) == SUCCESS;
}
