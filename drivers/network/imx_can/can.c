// TODO fill this out

// What mode does it start in on startup???

// << Reset >>
// Hard reset -- is chip level (assume power?)
// Soft reset 
// -- assert MCR[SOFTRST] -- this resets some of the memory mappe registers synchronously.
// -- MCR[SOFTRST] will remain asserted while soft reset is pending (it needs to propogate as is synchronous). Can poll this until deasserted to indicate soft-reset is complete

// << Init >>
// Required that FlexCAN be put into Freeze mode to initialize (must be initialized after every reset).


// Alternate way to start is to try and just read device registers to check connected to the board correctly
// start by attempting to read, write and poll the MCR reset register to determine if we're actually able to connect to the board or not