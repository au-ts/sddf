use sel4_microkit::MessageInfo;

enum SddfTimer {
    GetTime = 0,
    SetTimeout = 1,
}

pub struct Timer {
    channel: sel4_microkit::Channel,
}

impl Timer {
    pub const fn new(server_channel: sel4_microkit::Channel) -> Self {
        Timer {
            channel: server_channel,
        }
    }

    pub fn set_timeout(&self, timeout: u64) {
        sel4_microkit::set_mr(0, timeout);
        let msg_info: MessageInfo = MessageInfo::new(SddfTimer::SetTimeout as u64, 1);
        self.channel.pp_call(msg_info);
    }

    pub fn time_now(&self) -> u64 {
        let msg_info: MessageInfo = MessageInfo::new(SddfTimer::GetTime as u64, 0);
        self.channel.pp_call(msg_info);
        sel4_microkit::get_mr(0)
    }
}
