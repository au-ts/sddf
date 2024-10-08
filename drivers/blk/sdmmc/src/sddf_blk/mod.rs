extern "C" {
    pub fn blk_queue_init_helper();

    pub fn blk_queue_empty_req_helper() -> u8;
    pub fn blk_queue_full_resp_helper() -> u8;
    pub fn blk_enqueue_resp_helper(status: BlkStatus, success: u32, id: u32) -> u8;
    pub fn blk_dequeue_req_helper(code: *mut BlkOp,
                                io_or_offset: *mut u64,
                                block_number: *mut u32,
                                count: *mut u16,
                                id: *mut u32);
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
    pub block_number: u32,
    pub count: u16,
    // I suggest use u32 here and change the count to use u32 in sddf_blk
    pub success_count: u32,
    pub count_to_do: u32,
    pub id: u32,
}