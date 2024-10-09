use core::{future::Future, pin::Pin, task::{Context, Poll, Waker}};

use sdmmc_constant::{MMC_CMD_READ_MULTIPLE_BLOCK, MMC_CMD_READ_SINGLE_BLOCK, MMC_CMD_STOP_TRANSMISSION, MMC_CMD_WRITE_MULTIPLE_BLOCK, MMC_CMD_WRITE_SINGLE_BLOCK};
mod sdmmc_constant;
pub struct SdmmcCmd {
    pub cmdidx: u32,
    pub resp_type: u32,
    pub cmdarg: u32,
}

pub struct MmcData {
    // The size of the block(sector size), for sdcard should almost always be 512
    pub blocksize: u32,
    // Number of blocks to transfer
    pub blockcnt: u32,
    pub flags: MmcDataFlag,
    pub addr: u64,
}

pub enum MmcDataFlag {
    SdmmcDataRead,
    SdmmcDataWrite,
}

pub enum SdmmcHalError {
    // Error for result not ready yet
    EBUSY,
    ETIMEDOUT,
    EINVAL,
    EIO,
    ENOTIMPLEMENTED,
    // This error should not be triggered unless there are bugs in program
    EUNDEFINED,
    // The block transfer succeed, but fail to stop the read/write process
    ESTOPCMD,
}

// Interrupt related define
#[repr(u32)]  // Ensures the enum variants are stored as 32-bit integers
pub enum InterruptType {
    Success = 0b0001,    // 1st bit
    Error   = 0b0010,    // 2nd bit
    SDIO    = 0b0100,    // 3rd bit
    // You can add more flags as needed
}

// Define the MMC response flags
const MMC_RSP_PRESENT: u32 = 1 << 0;
const MMC_RSP_136: u32 = 1 << 1;       // 136-bit response
const MMC_RSP_CRC: u32 = 1 << 2;       // Expect valid CRC
const MMC_RSP_BUSY: u32 = 1 << 3;      // Card may send busy
const MMC_RSP_OPCODE: u32 = 1 << 4;    // Response contains opcode

// Define the MMC response types
pub const MMC_RSP_NONE: u32 = 0;
pub const MMC_RSP_R1: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;
pub const MMC_RSP_R1B: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE | MMC_RSP_BUSY;
pub const MMC_RSP_R2: u32 = MMC_RSP_PRESENT | MMC_RSP_136 | MMC_RSP_CRC;
pub const MMC_RSP_R3: u32 = MMC_RSP_PRESENT;
pub const MMC_RSP_R4: u32 = MMC_RSP_PRESENT;
pub const MMC_RSP_R5: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;
pub const MMC_RSP_R6: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;
pub const MMC_RSP_R7: u32 = MMC_RSP_PRESENT | MMC_RSP_CRC | MMC_RSP_OPCODE;


/// Program async Rust can be very dangerous if you do not know what is happening understand the hood
/// Power up and power off cannot be properly implemented if I do not have access to control gpio/ regulator and timer
pub trait SdmmcHardware {
    fn sdmmc_power_up(&mut self) -> Result<(), SdmmcHalError> {
        return Err(SdmmcHalError::ENOTIMPLEMENTED);
    }

    fn sdmmc_set_ios(&mut self) -> Result<(), SdmmcHalError> {
        return Err(SdmmcHalError::ENOTIMPLEMENTED);
    }

    fn sdmmc_send_command(&mut self, cmd: &SdmmcCmd, data: Option<&MmcData>) -> Result<(), SdmmcHalError> {
        return Err(SdmmcHalError::ENOTIMPLEMENTED);
    }

    fn sdmmc_receive_response(&self, cmd: &SdmmcCmd, response: &mut [u32; 4]) -> Result<(), SdmmcHalError> {
        return Err(SdmmcHalError::ENOTIMPLEMENTED);
    }

    fn sdmmc_enable_interrupt(&mut self, irq_to_enable: &mut u32) -> Result<(), SdmmcHalError> {
        return Err(SdmmcHalError::ENOTIMPLEMENTED);
    }

    fn sdmmc_ack_interrupt(&mut self, irq_enabled: &u32) -> Result<(), SdmmcHalError> {
        return Err(SdmmcHalError::ENOTIMPLEMENTED);
    }

    fn sdmmc_power_off(&mut self) -> Result<(), SdmmcHalError> {
        return Err(SdmmcHalError::ENOTIMPLEMENTED);
    }
}

fn send_cmd_and_receive_resp<T: SdmmcHardware>(
    hardware: &mut T,
    cmd: &SdmmcCmd,
    data: Option<&MmcData>,
    resp: &mut [u32; 4]
) -> Result<(), SdmmcHalError> {
    // Send the command using the hardware layer
    let mut res = hardware.sdmmc_send_command(cmd, data);
    if res.is_err() {
        return res;
    }

    // TODO: Change it to use the sleep function provided by the hardware layer
    let mut retry: u32 = 1000000;
    
    while retry > 0 {
        // Try to receive the response
        res = hardware.sdmmc_receive_response(cmd, resp);
        
        if let Err(SdmmcHalError::EBUSY) = res {
            // Busy response, retry
            retry -= 1;
            // hardware.sleep(1); // Placeholder: Implement a sleep function in SdmmcHardware trait
        } else {
            // If any other error or success, break the loop
            break;
        }
    }

    res // Return the final result (Ok or Err)
}

/// TODO: Add more variables for SdmmcProtocol to track the state of the sdmmc controller and card correctly
pub struct SdmmcProtocol<'a, T: SdmmcHardware> {
    pub hardware: &'a mut T,
    enabled_irq: u32,
}

impl<T> Unpin for SdmmcProtocol<'_, T> where T: Unpin + SdmmcHardware {}

impl<'a, T: SdmmcHardware> SdmmcProtocol<'a, T> {
    pub fn new(hardware: &'a mut T) -> Self {
        SdmmcProtocol {
            hardware,
            enabled_irq: 0,
        }
    }

    pub fn reset_card(&mut self) -> Result<(), SdmmcHalError> {
        let all: u32 = InterruptType::Success as u32 | InterruptType::Error as u32 | InterruptType::SDIO as u32;
        self.hardware.sdmmc_ack_interrupt(&all)
    }

    pub fn enable_interrupt(&mut self, irq_to_enable: &mut u32) -> Result<(), SdmmcHalError> {
        let res = self.hardware.sdmmc_enable_interrupt(irq_to_enable);
        self.enabled_irq = *irq_to_enable;
        res
    }

    pub fn ack_interrupt(&mut self) -> Result<(), SdmmcHalError> {
        self.hardware.sdmmc_ack_interrupt(&self.enabled_irq)
    }

    pub async fn read_block(self, blockcnt: u32, start_idx: u64, destination: u64) -> (Result<(), SdmmcHalError>, Option<SdmmcProtocol<'a, T>>) {
        let mut cmd: SdmmcCmd;
        let mut res: Result<(), SdmmcHalError>;
        // TODO: Figure out a way to support cards with 4 KB sector size
        let data: MmcData = MmcData {
            blocksize: 512,
            blockcnt,
            flags: MmcDataFlag::SdmmcDataRead,
            addr: destination,
        };
        let mut resp: [u32; 4] = [0; 4];
        // TODO: Add more validation check in the future
        // Like sdmmc card usually cannot transfer arbitrary number of blocks at once

        // The cmd arg for read operation is different between some card variation as showed by uboot code below
        /*
            if (mmc->high_capacity)
                cmd.cmdarg = start;
            else
                cmd.cmdarg = start * mmc->read_bl_len;
        */
        // For now we default to assume the card is high_capacity
        // TODO: Fix it when we properly implement card boot up
        // TODO: If we boot the card by ourself or reset the card, remember to send block len cmd
        let cmd_arg: u64 = start_idx;
        if blockcnt == 1 {
            cmd = SdmmcCmd {
                cmdidx: MMC_CMD_READ_SINGLE_BLOCK,
                resp_type: MMC_RSP_R1,
                cmdarg: cmd_arg as u32,
            };
            let future = SdmmcCmdFuture::new(self.hardware, &cmd, Some(&data), &mut resp);
            res = future.await;

            // TODO: Figure out a generic model for every sd controller, like what if the sd controller only send interrupt
            // for read/write requests?
            let _ = self.hardware.sdmmc_ack_interrupt(&self.enabled_irq);

            return (res, Some(self));
        }
        else {
            cmd = SdmmcCmd {
                cmdidx: MMC_CMD_READ_MULTIPLE_BLOCK,
                resp_type: MMC_RSP_R1,
                cmdarg: cmd_arg as u32,
            };
            let future = SdmmcCmdFuture::new(self.hardware, &cmd, Some(&data), &mut resp);
            res = future.await;

            // TODO: Figure out a generic model for every sd controller, like what if the sd controller only send interrupt
            // for read/write requests?
            let _ = self.hardware.sdmmc_ack_interrupt(&self.enabled_irq);
    
            if let Ok(()) = res {
                // Uboot code for determine response type in this case
                // cmd.resp_type = (IS_SD(mmc) || write) ? MMC_RSP_R1b : MMC_RSP_R1;
                // TODO: Add mmc checks here
                cmd = SdmmcCmd {
                    cmdidx: MMC_CMD_STOP_TRANSMISSION,
                    resp_type: MMC_RSP_R1B,
                    cmdarg: 0,
                };
                let future = SdmmcCmdFuture::new(self.hardware, &cmd, None, &mut resp);
                res = future.await;

                // TODO: Figure out a generic model for every sd controller, like what if the sd controller only send interrupt
                // for read/write requests?
                let _ = self.hardware.sdmmc_ack_interrupt(&self.enabled_irq);

                return (res.map_err(|_| SdmmcHalError::ESTOPCMD), Some(self));
            } else {
                return (res, Some(self));
            }
        }
    }

    // Almost the same with read_block aside from the cmd being sent is a bit different
    // For any future code add to read_block/write_block, remember to change both
    // Should read_block/write_block be the same function?
    pub async fn write_block(self, blockcnt: u32, start_idx: u64, source: u64) -> (Result<(), SdmmcHalError>, Option<SdmmcProtocol<'a, T>>) {
        let mut cmd: SdmmcCmd;
        let mut res: Result<(), SdmmcHalError>;
        // TODO: Figure out a way to support cards with 4 KB sector size
        let data: MmcData = MmcData {
            blocksize: 512,
            blockcnt,
            flags: MmcDataFlag::SdmmcDataWrite,
            addr: source,
        };
        let mut resp: [u32; 4] = [0; 4];
        // TODO: Add more validation check in the future

        let cmd_arg: u64 = start_idx;
        if blockcnt == 1 {
            cmd = SdmmcCmd {
                cmdidx: MMC_CMD_WRITE_SINGLE_BLOCK,
                resp_type: MMC_RSP_R1,
                cmdarg: cmd_arg as u32,
            };
            let future = SdmmcCmdFuture::new(self.hardware, &cmd, Some(&data), &mut resp);
            res = future.await;

            // TODO: Figure out a generic model for every sd controller, like what if the sd controller only send interrupt
            // for read/write requests?
            let _ = self.hardware.sdmmc_ack_interrupt(&self.enabled_irq);

            return (res, Some(self));
        }
        else {
            cmd = SdmmcCmd {
                cmdidx: MMC_CMD_WRITE_MULTIPLE_BLOCK,
                resp_type: MMC_RSP_R1,
                cmdarg: cmd_arg as u32,
            };
            let future = SdmmcCmdFuture::new(self.hardware, &cmd, Some(&data), &mut resp);
            res = future.await;

            // TODO: Figure out a generic model for every sd controller, like what if the sd controller only send interrupt
            // for read/write requests?
            let _ = self.hardware.sdmmc_ack_interrupt(&self.enabled_irq);

            if let Ok(()) = res {
                // Uboot code for determine response type in this case
                // cmd.resp_type = (IS_SD(mmc) || write) ? MMC_RSP_R1b : MMC_RSP_R1;
                // TODO: Add mmc checks here
                cmd = SdmmcCmd {
                    cmdidx: MMC_CMD_STOP_TRANSMISSION,
                    resp_type: MMC_RSP_R1B,
                    cmdarg: 0,
                };
                let future = SdmmcCmdFuture::new(self.hardware, &cmd, None, &mut resp);
                res = future.await;
                
                // TODO: Figure out a generic model for every sd controller, like what if the sd controller only send interrupt
                // for read/write requests?
                let _ = self.hardware.sdmmc_ack_interrupt(&self.enabled_irq);

                return (res.map_err(|_| SdmmcHalError::ESTOPCMD), Some(self));
            } else {
                return (res, Some(self));
            }
        }
    }
}

enum CmdState {
    // Currently sending the command
    // State at the start
    NotSent,
    // Waiting for the response
    WaitingForResponse,
    // Error encountered
    Error,
    // Finished
    Finished,
}

pub struct SdmmcCmdFuture<'a, 'b, 'c> {
    hardware: &'a mut dyn SdmmcHardware,
    cmd: &'b SdmmcCmd,
    data: Option<&'b MmcData>,
    waker: Option<Waker>,
    state: CmdState,
    response: &'c mut [u32; 4],
}

impl<'a, 'b, 'c> SdmmcCmdFuture<'a, 'b, 'c> {
    pub fn new(
        hardware: &'a mut dyn SdmmcHardware,
        cmd: &'b SdmmcCmd,
        data: Option<&'b MmcData>,
        response: &'c mut [u32; 4]) -> SdmmcCmdFuture<'a, 'b, 'c> {
        SdmmcCmdFuture {
            hardware,
            cmd,
            data,
            waker: None,
            state: CmdState::NotSent,
            response,
        }
    }
}

/// SdmmcCmdFuture serves as the basic building block for async fn above
/// In the context of Sdmmc device, since the requests are executed linearly under the hood
/// We actually do not need an executor to execute the request
/// The context can be ignored unless someone insist to use an executor for the requests
/// So for now, the context is being stored in waker but this waker will not be used
/// Beside, we are in no std environment and can barely use any locks
impl<'a, 'b, 'c> Future for SdmmcCmdFuture<'a, 'b, 'c> {
    type Output = Result<(), SdmmcHalError>;

     fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // As I have said above, this waker is not being used so it do not need to be shared data
        // But store the waker provided anyway
        // Beware you need to update waker every polling, for more details about why
        // read Asynchronous Programming in Rust
        self.waker = Some(cx.waker().clone());

        match self.state {
            CmdState::NotSent => {
                let res: Result<(), SdmmcHalError>;
                {
                    let this: &mut SdmmcCmdFuture<'a, 'b, 'c> = self.as_mut().get_mut();

                    // Now, you can pass `&SdmmcCmd` to `sdmmc_send_command`
                    let cmd: &SdmmcCmd = this.cmd;
                    let data: Option<&MmcData> = this.data;
                    res = this.hardware.sdmmc_send_command(cmd, data);
                }
                if let Ok(()) = res {
                    self.state = CmdState::WaitingForResponse;
                    return Poll::Pending;
                } else {
                    self.state = CmdState::Error;
                    return Poll::Ready(res);
                }
            }
            CmdState::WaitingForResponse => {
                let res;
                {
                    let this: &mut SdmmcCmdFuture<'a, 'b, 'c> = self.as_mut().get_mut();
                    let cmd: &SdmmcCmd = this.cmd;
                    let response: &mut [u32; 4] = this.response;
                    let hardware: &mut dyn SdmmcHardware = this.hardware;
                    res = hardware.sdmmc_receive_response(cmd, response);
                }
                if let Err(SdmmcHalError::EBUSY) = res {
                    return Poll::Pending;
                } else if let Ok(()) = res {
                    self.state = CmdState::Finished;
                    return Poll::Ready(res);
                } else {
                    self.state = CmdState::Error;
                    return Poll::Ready(res);
                }
            }
            CmdState::Error => return Poll::Ready(Err(SdmmcHalError::EUNDEFINED)),
            CmdState::Finished => return Poll::Ready(Err(SdmmcHalError::EUNDEFINED)),
        }
    }
}