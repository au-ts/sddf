/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/pcie/protocol.h>
#include <sddf/util/util.h>

sddf_pcie_status_t pcie_claim_device(unsigned int channel, uint8_t spec_idx, sddf_pcie_handle_t *handle)
{
    return SDDF_PCIE_STATUS_OK;
}

sddf_pcie_status_t pcie_read_config_space_8(unsigned int channel, sddf_pcie_handle_t handle, uint16_t offset,
                                            uint8_t *value)
{
    return SDDF_PCIE_STATUS_OK;
}

sddf_pcie_status_t pcie_read_config_space_16(unsigned int channel, sddf_pcie_handle_t handle, uint16_t offset,
                                             uint16_t *value)
{
    return SDDF_PCIE_STATUS_OK;
}

sddf_pcie_status_t pcie_read_config_space_32(unsigned int channel, sddf_pcie_handle_t handle, uint16_t offset,
                                             uint32_t *value)
{
    return SDDF_PCIE_STATUS_OK;
}

sddf_pcie_status_t pcie_get_mem_bar(unsigned int channel, sddf_pcie_handle_t handle, uint8_t bar_index,
                                    uint64_t *bar_size, bool *is_64b, bool *prefetchable)
{
    return SDDF_PCIE_STATUS_OK;
}

sddf_pcie_status_t pcie_map_mem_bar(unsigned int channel, sddf_pcie_handle_t handle, uint8_t bar_index,
                                    uint64_t map_addr, sddf_pcie_mem_attr_t attributes, bool read_write)
{
    return SDDF_PCIE_STATUS_OK;
}

sddf_pcie_status_t pcie_map_intx(unsigned int channel, sddf_pcie_handle_t handle, uint64_t ch_id)
{
    return SDDF_PCIE_STATUS_OK;
}

sddf_pcie_status_t pcie_ack_intx(unsigned int channel, sddf_pcie_handle_t handle)
{
    return SDDF_PCIE_STATUS_OK;
}
