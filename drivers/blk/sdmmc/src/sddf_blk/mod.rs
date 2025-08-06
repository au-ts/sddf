// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

unsafe extern "C" {
    pub unsafe fn blk_queue_init_helper(capacity: u64);

    pub unsafe fn blk_device_regs_vaddr() -> u64;
    pub unsafe fn blk_device_init_data_vaddr() -> u64;
    pub unsafe fn blk_device_init_data_ioaddr() -> u64;

    pub unsafe fn blk_queue_empty_req_helper() -> u8;
    pub unsafe fn blk_queue_full_resp_helper() -> u8;
    pub unsafe fn blk_enqueue_resp_helper(status: BlkStatus, success: u16, id: u32) -> u8;
    pub unsafe fn blk_dequeue_req_helper(
        code: *mut BlkOp,
        io_or_offset: *mut u64,
        block_number: *mut u64,
        count: *mut u16,
        id: *mut u32,
    );
}

#[repr(C)]
pub enum BlkOp {
    BlkReqRead,
    BlkReqWrite,
    BlkReqFlush,
    BlkReqBarrier,
}

#[repr(C)]
pub enum BlkStatus {
    BlkRespOk,
    BlkRespSeekError,
}

pub struct BlkRequest {
    pub request_code: BlkOp,
    pub io_or_offset: u64,
    pub block_number: u64,
    pub count: u32,
    // I suggest use u32 here and change the count to use u32 in sddf_blk
    pub success_count: u32,
    pub count_to_do: u32,
    pub id: u32,
}
