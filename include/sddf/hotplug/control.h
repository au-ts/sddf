/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>

/**
 * For the controller and drivers to communicate.
 */

#define SDDF_HOTPLUG_REQ_INSERT  1
#define SDDF_HOTPLUG_REQ_EJECT   2

/* wait for an state change interrupt  */
#define SDDF_HOTPLUG_RESP_OK      1
/* we're already in this state */
#define SDDF_HOTPLUG_RESP_NOOP    2
/* we couldn't do this as we were already doing something else */
#define SDDF_HOTPLUG_RESP_INVALID_OPERATION   3
/* there is no device */
#define SDDF_HOTPLUG_RESP_NO_DEV  4
