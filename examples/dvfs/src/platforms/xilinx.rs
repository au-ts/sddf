use cpufreq::freq_trait::{FreqOps, OppEntry};

pub const OPP_TABLE: &[OppEntry] = &[
    OppEntry {
        freq_hz: 1199999988,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
    OppEntry {
        freq_hz: 599999994,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
    OppEntry {
        freq_hz: 399999996,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
    OppEntry {
        freq_hz: 299999997,
        voltage_uv: 1000000,
        latency_ns: 500000,
    },
];

pub const CPU_OPP_TABLE: &[&[OppEntry]] = &[
    OPP_TABLE, 
    OPP_TABLE,
    OPP_TABLE,
    OPP_TABLE,
];

pub struct Xilinx {}

impl FreqOps for Xilinx {
    const CPU_OPP_TABLE: &[&[OppEntry]] = CPU_OPP_TABLE;
}