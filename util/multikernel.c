/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifdef MULTIKERNEL
#include <sddf/util/multikernel.h>

/* Microkit will patch this with the address of the config blob on a per PD basis.
 * Avoid multiple definitions in a single PD ELF by keeping this defined in this '.c'
 */
const sddf_multikernel_config_t *sddf_multikernel_config;
#endif
