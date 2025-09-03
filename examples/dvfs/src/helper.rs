unsafe extern "C" {
    pub unsafe fn wait();

    pub unsafe fn print_count(cycle: u64);

    pub unsafe fn counter_init();

    pub unsafe fn read_count() -> u64;
}