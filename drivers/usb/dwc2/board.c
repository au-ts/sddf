/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#if CFG_TUSB_MCU == OPT_MCU_BCM2711 && BCM_VERSION == 2711
    #include <broadcom/vcmailbox.h>

    void board_init(void)
    {
        vcmailbox_set_power_state(VCMAILBOX_DEVICE_USB_HCD, true);
    }
#endif
