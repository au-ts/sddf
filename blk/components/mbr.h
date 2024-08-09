#pragma once

int client_get_drv_block_number(int cli_id, uint32_t cli_block_number, blk_req_code_t cli_code, uint16_t cli_count, uint32_t *ret_drv_block_number);

bool setup_clients(fsmalloc_t *fsmalloc, ialloc_t *ialloc, blk_queue_handle_t *drv_h, microkit_channel driver_ch);
