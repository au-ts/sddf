/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <sddf/network/lib_sddf_lwip.h>
#include "lwip/pbuf.h"

/**
 * This library supports hardware checksum generation for the GENET NIC. For
 * GENET NIC checksum offload, the first bytes before each packet must contain
 * metadata pertaining to where the checksum should be written within the
 * packet, as well as which bytes the checksum should be summed over.
 *
 * Additionally, for transport layer protocols requiring a pseudo-header
 * checksum, this must already be present in the transport layer checksum
 * header.
 *
 * The library works by appending an lwip pbuf containing this metadata to each
 * outgoing packet, and, if needed, setting the transport layer checksum to the
 * pseudo-header checksum.
 */

 /**
  * Lib sDDF lwIP function for `tx_intercept_condition`. Checks whether the
  * checksum metadata pbuf has been appended to the outgoing pbuf.
  *
  * @param p pbuf to be transmitted via sDDF.
  *
  * @return true checksum has NOT been appended, thus transmission must be
  * intercepted.
  * @return false checksum has been appended, transmission may continue.
  */
bool pbuf_needs_checksum(struct pbuf *p);

/**
 * Lib sDDF lwIP function for `tx_handle_intercept`. Appends a static pbuf
 * containing checksum metadata to the provided outgoing pbuf p, then transmits
 * the pbuf using `sddf_lwip_transmit_pbuf`. If the outgoing pbuf contains a
 * packet which requires a pseudo-header calculation, this function will add the
 * partial checksum to the transport-layer header.
 *
 * @param p pbuf to be transmitted via sDDF.
 * @return net_sddf_err_t error result of concatenated pbuf transmission.
 */
net_sddf_err_t add_checksum_and_transmit(struct pbuf *p);
