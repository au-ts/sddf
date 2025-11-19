// Copyright 2025, UNSW
// SPDX-License-Identifier: BSD-2-Clause

use core::convert::Infallible;

use num_enum::{IntoPrimitive, TryFromPrimitive};
use sddf_ipc_types::{
    MessagParseError, MessageBuilder, MessageParser, MessageWriter, ReadFromMessage,
};

#[derive(Debug)]
pub enum DvfsReq {
    GetFreq { core_ident: u64 },
    SetFreq { core_ident: u64, freq_hz: u64 },
}

#[derive(IntoPrimitive, TryFromPrimitive)]
#[cfg_attr(target_pointer_width = "32", repr(u32))]
#[cfg_attr(target_pointer_width = "64", repr(u64))]
#[derive(Debug)]
enum DvfsMessageLabel {
    GetFreq = 0,
    SetFreq = 1,
}

#[derive(Debug)]
pub enum DvfsResp {
    Error,
    GetFreq { freq_hz: u64 },
    SetFreq,
}

#[derive(IntoPrimitive, TryFromPrimitive)]
#[cfg_attr(target_pointer_width = "32", repr(u32))]
#[cfg_attr(target_pointer_width = "64", repr(u64))]
#[derive(Debug)]
enum DvfsRespLabel {
    Success = 0,
    Error = 1,
}

impl ReadFromMessage for DvfsReq {
    type Error = MessagParseError;

    fn read_from_message(
        label: sddf_ipc_types::MessageLabel,
        buf: &[sddf_ipc_types::MessageRegisterValue],
    ) -> Result<Self, Self::Error> {
        let parser = MessageParser::new(label, buf);
        Ok(match parser.label_try_into()? {
            DvfsMessageLabel::GetFreq => {
                let mut i = 0..;
                let core_ident = parser.get_mr(i.next().unwrap())?;
                DvfsReq::GetFreq { core_ident }
            }
            DvfsMessageLabel::SetFreq => {
                let mut i = 0..;
                let core_ident = parser.get_mr(i.next().unwrap())?;
                let freq_hz = parser.get_mr(i.next().unwrap())?;
                DvfsReq::SetFreq {
                    core_ident,
                    freq_hz,
                }
            }
        })
    }
}

impl MessageWriter for DvfsResp {
    type Error = Infallible;

    fn write_message(
        &self,
        buf: &mut [sddf_ipc_types::MessageRegisterValue],
    ) -> Result<(sddf_ipc_types::MessageLabel, usize), <DvfsResp as MessageWriter>::Error> {
        let mut builder = MessageBuilder::new(buf);

        let mut i = 0..;
        match self {
            DvfsResp::Error => {
                builder.set_mr(i.next().unwrap(), DvfsRespLabel::Error as u64);
            }
            DvfsResp::GetFreq { freq_hz } => {
                builder.set_mr(i.next().unwrap(), DvfsRespLabel::Success as u64);
                builder.set_mr(i.next().unwrap(), *freq_hz);
            }
            DvfsResp::SetFreq => {
                builder.set_mr(i.next().unwrap(), DvfsRespLabel::Success as u64);
            }
        }

        Ok(builder.build())
    }
}
