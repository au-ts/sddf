// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

#![no_std] // Don't link the standard library
#![no_main] // Don't use the default entry point
#![feature(used_with_arg)]

extern crate alloc;

mod sddf_blk;
mod sel4_microkit_os;

use core::{
    future::Future, mem::MaybeUninit, pin::Pin, task::{Context, Poll, RawWaker, RawWakerVTable, Waker}
};

use alloc::boxed::Box;
use sddf_blk::{
    BlkOp, BlkRequest, BlkStatus, blk_dequeue_req_helper, blk_device_init_data_ioaddr,
    blk_device_init_data_vaddr, blk_device_regs_vaddr, blk_enqueue_resp_helper,
    blk_queue_empty_req_helper, blk_queue_full_resp_helper, blk_queue_init_helper,
};

use crate::sel4_microkit_os::{SerialOps, TimerOps, platform::VOLTAGE};

extern "C" {
    pub static mut device_resources: DeviceResources;
    pub static mut config: BlkDriverConfig;
}

const INTERRUPT: u32 = unsafe { device_resources.irqs[0].id };
const BLK_VIRTUALIZER: u32 = unsafe { config.virt.id };
const TIMER: TimerOps = TimerOps::new();
const SERIAL: SerialOps = SerialOps::new();
const HOST_INFO: HostInfo = crate::sel4_microkit_os::platform::host_info();

use sdmmc_protocol::{
    sdmmc::{mmc_struct::CardInfo, HostInfo, SDCARD_DEFAULT_SECTOR_SIZE},
    sdmmc_traits::SdmmcHardware,
};
use sdmmc_protocol::{
    sdmmc::{SdmmcError, SdmmcProtocol},
    sdmmc_os::{Sleep, VoltageOps},
};

const SDDF_TRANSFER_SIZE: u32 = 4096;
const SDDF_TO_REAL_SECTOR: u32 = SDDF_TRANSFER_SIZE / SDCARD_DEFAULT_SECTOR_SIZE;

struct HandlerImpl<T: SdmmcHardware, S: Sleep, V: VoltageOps> {
    future: Option<Pin<Box<dyn Future<Output = (Result<(), SdmmcError>, SdmmcProtocol<T, S, V>)>>>>,
    sdmmc: Option<SdmmcProtocol<T, S, V>>,
    request: Option<BlkRequest>,
    card_info: CardInfo,
}

pub static mut handler: MaybeUninit<HandlerImpl<T, S, V>> = MaybeUninit::uninit();

// No-op waker implementations, they do nothing.
unsafe fn noop(_data: *const ()) {}
unsafe fn noop_clone(_data: *const ()) -> RawWaker {
    RawWaker::new(_data, &VTABLE)
}

/// Since in .system file, the page we are providing to tune_performance function is uncached
/// we do not need to provide a real cache invalidate function
fn dummy_cache_invalidate_function() {}

// A VTable that points to the no-op functions
static VTABLE: RawWakerVTable = RawWakerVTable::new(noop_clone, noop, noop, noop);

// Function to create a dummy Waker
fn create_dummy_waker() -> Waker {
    let raw_waker = RawWaker::new(core::ptr::null(), &VTABLE);
    unsafe { Waker::from_raw(raw_waker) }
}

pub fn init() {
    unsafe {
        sdmmc_protocol::sdmmc_os::set_logger(&SERIAL).unwrap();
    }

    let regs_base = unsafe { blk_device_regs_vaddr() };

    let hal = unsafe { crate::sel4_microkit_os::platform::platform_hal(regs_base) };

    let unsafe_stolen_memory: &mut [u8; 64];

    // This line of code actually is very unsafe!
    // Considering the memory is stolen from the memory that has sdcard registers mapped in
    // A data region for card init is needed because some information is passed to the driver
    // by the card transferring data to normal memory instead of reading a register.
    let init_data_vaddr = unsafe { blk_device_init_data_vaddr() };
    let init_data_ioaddr = unsafe { blk_device_init_data_ioaddr() };

    unsafe {
        let stolen_memory_addr = init_data_vaddr as *mut [u8; 64];
        assert!(stolen_memory_addr as usize % 8 == 0);
        unsafe_stolen_memory = &mut (*stolen_memory_addr);
    }

    // Handling result in two different ways, by matching and unwrap_or_else
    let res = SdmmcProtocol::new(hal, TIMER, Some(VOLTAGE));
    let mut sdmmc_host = match res {
        Ok(host) => host,
        Err(err) => panic!("SDMMC: Error at init {:?}", err),
    };

    sdmmc_host
        .setup_card()
        .unwrap_or_else(|error| panic!("SDMMC: Error at setup {:?}", error));

    sdmmc_host.print_card_info();

    let card_info: CardInfo = sdmmc_host.card_info().unwrap();

    let _ = sdmmc_host.config_interrupt(false, false);

    // Should tuning be possible to fail?
    unsafe {
        sdmmc_host
            .tune_performance(
                unsafe_stolen_memory,
                dummy_cache_invalidate_function,
                init_data_ioaddr,
            )
            .unwrap_or_else(|error| panic!("SDMMC: Error at tuning performance {:?}", error));
    }

    // Should always succeed, at least for odroid C4
    let _ = sdmmc_host.config_interrupt(true, false);

    unsafe {
        blk_queue_init_helper(card_info.card_capacity);
    }

    unsafe { handler.write(HandlerImpl { future: None, sdmmc: Some(sdmmc_host), request: None, card_info }) };
}

fn notified(channel_set: ChannelSet) {
    for channel in channel_set.iter() {
        if channel.index() != INTERRUPT.index() && channel.index() != BLK_VIRTUALIZER.index() {
            sel4::debug_println!(
                "SDMMC_DRIVER: Unknown channel sent me message: {}",
                channel.index()
            );
            return;
        }

        let mut notify_virt: bool = false;
        let init_handler = unsafe { handler.assume_init() };

        'process_notification: {
            // Polling if receive interrupt notification
            if channel.index() == INTERRUPT.index() {
                if let Some(request) = &mut init_handler.request {
                    if let Some(future) = &mut init_handler.future {
                        let waker = create_dummy_waker();
                        let mut cx = Context::from_waker(&waker);
                        match future.as_mut().poll(&mut cx) {
                            Poll::Ready((result, sdmmc)) => {
                                init_handler.future = None; // Reset the future once done
                                init_handler.sdmmc = Some(sdmmc);
                                if result.is_ok() {
                                    // Deduct finished count from count
                                    request.success_count += request.count_to_do;
                                    request.count -= request.count_to_do;

                                    if request.count == 0 {
                                        let resp_status = BlkStatus::BlkRespOk;
                                        notify_virt = true;
                                        unsafe {
                                            // The using try_into() to convert u32 to u16 should not be necessary unless
                                            // there are bugs in the code cause the operation to fail
                                            blk_enqueue_resp_helper(
                                                resp_status,
                                                (request.success_count / SDDF_TO_REAL_SECTOR)
                                                    .try_into()
                                                    .unwrap(),
                                                request.id,
                                            );
                                        }
                                        init_handler.request = None;
                                    }
                                } else {
                                    let resp_status = BlkStatus::BlkRespSeekError;
                                    notify_virt = true;
                                    unsafe {
                                        blk_enqueue_resp_helper(
                                            resp_status,
                                            (request.success_count / SDDF_TO_REAL_SECTOR)
                                                .try_into()
                                                .unwrap(),
                                            request.id,
                                        );
                                    }
                                    init_handler.request = None;
                                }
                            }
                            Poll::Pending => {
                                // Since the future is not ready, no other request can be dequeued, exit the big loop
                                break 'process_notification;
                            }
                        }
                    } else {
                        panic!(
                            "SDMMC: Receive a hardware interrupt despite not having a future!"
                        );
                    }
                }
            }

            while init_handler.request.is_none()
                && unsafe {
                    blk_queue_empty_req_helper() == 0 && blk_queue_full_resp_helper() == 0
                }
            {
                let mut request: BlkRequest = BlkRequest {
                    request_code: BlkOp::BlkReqFlush,
                    io_or_offset: 0,
                    block_number: 0,
                    count: 0,
                    success_count: 0,
                    count_to_do: 0,
                    id: 0,
                };
                let mut sddf_count: u16 = 0;
                unsafe {
                    blk_dequeue_req_helper(
                        &mut request.request_code as *mut BlkOp,
                        &mut request.io_or_offset as *mut u64,
                        &mut request.block_number as *mut u64,
                        &mut sddf_count as *mut u16,
                        &mut request.id as *mut u32,
                    );
                }
                // TODO: Consider to add integer overflow check here
                request.block_number = request.block_number * SDDF_TO_REAL_SECTOR as u64;
                request.count = (sddf_count as u32) * SDDF_TO_REAL_SECTOR;

                // Print the retrieved values
                #[cfg(feature = "dev-logs")]
                {
                    sel4::debug_println!("io_or_offset: 0x{:x}", request.io_or_offset); // Simple u64
                    sel4::debug_println!("block_number: {}", request.block_number); // Simple u32
                    sel4::debug_println!("count: {}", request.count); // Simple u16
                    sel4::debug_println!("id: {}", request.id); // Simple u32
                }

                // Check if the request is valid
                if (request.count as u64 + request.block_number as u64)
                    * SDCARD_DEFAULT_SECTOR_SIZE as u64
                    > init_handler.card_info.card_capacity
                {
                    unsafe {
                        blk_enqueue_resp_helper(BlkStatus::BlkRespSeekError, 0, request.id);
                    }
                }

                match request.request_code {
                    BlkOp::BlkReqRead => {
                        init_handler.request = Some(request);
                        break;
                    }
                    BlkOp::BlkReqWrite => {
                        init_handler.request = Some(request);
                        break;
                    }
                    _ => {
                        // For other request, enqueue response
                        notify_virt = true;
                        unsafe {
                            blk_enqueue_resp_helper(BlkStatus::BlkRespOk, 0, request.id);
                        }
                    }
                }
            }

            // If future is empty
            if let Some(request) = &mut init_handler.request {
                if let None = init_handler.future {
                    match request.request_code {
                        BlkOp::BlkReqRead => {
                            request.count_to_do =
                                core::cmp::min(request.count, HOST_INFO.max_block_per_req);
                            if let Some(sdmmc) = init_handler.sdmmc.take() {
                                init_handler.future = Some(Box::pin(sdmmc.read_block(
                                    request.count_to_do,
                                    request.block_number as u64 + request.success_count as u64,
                                    request.io_or_offset
                                        + request.success_count as u64
                                            * SDCARD_DEFAULT_SECTOR_SIZE as u64,
                                )));
                            } else {
                                panic!(
                                    "SDMMC_DRIVER: The sdmmc should be here since the future should be empty!!!"
                                )
                            }
                        }
                        BlkOp::BlkReqWrite => {
                            request.count_to_do =
                                core::cmp::min(request.count, HOST_INFO.max_block_per_req);
                            if let Some(sdmmc) = init_handler.sdmmc.take() {
                                init_handler.future = Some(Box::pin(sdmmc.write_block(
                                    request.count_to_do,
                                    request.block_number as u64 + request.success_count as u64,
                                    request.io_or_offset
                                        + request.success_count as u64
                                            * SDCARD_DEFAULT_SECTOR_SIZE as u64,
                                )));
                            } else {
                                panic!(
                                    "SDMMC_DRIVER: The sdmmc should be here and the future should be empty!!!"
                                )
                            }
                        }
                        _ => {
                            panic!("SDMMC_DRIVER: You should not reach here!")
                        }
                    }
                    let waker = create_dummy_waker();
                    let mut cx = Context::from_waker(&waker);
                    // Poll the future once to make it start working!
                    if let Some(ref mut future) = init_handler.future {
                        match future.as_mut().poll(&mut cx) {
                            Poll::Ready(_) => {
                                panic!(
                                    "SDMMC: RECEIVED INVALID REQUEST! Check request validation code!"
                                );
                            }
                            Poll::Pending => break 'process_notification,
                        }
                    }
                }
            }
        }

        if notify_virt == true {
            // sel4::debug_println!("SDMMC_DRIVER: Notify the BLK_VIRTUALIZER!");
            sddf_notify(BLK_VIRTUALIZER);
        }
        // Ack irq
        if channel.index() == INTERRUPT {
            let err = channel.irq_ack();
            if err.is_err() {
                panic!("SDMMC: Cannot acknowledge interrupt for CPU!")
            }
        }
    }
}
