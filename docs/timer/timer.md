<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# sDDF Timer Subsystem

The timer subsystem provides a set of drivers to utilise **peripheral timers** and select **architectural timers** on various boards. These timers allow drivers and clients alike to request notifications after a certain delay in nanoseconds, permitting simple delayed notifications (`sleep_ns`) or the implementation of user-space schedulers, real-time systems, polling-mode drivers, watchdogs and more.

All timestamps in the sDDF are of type `sddf_timeout_t`, a 64 bit container for absolute timestamps in nanoseconds.


## Client interface

Clients have a page mapped into their address space which is shared with the virt, containing the time of the most recent timeout. This is intended to allow clients to locally handle coalesced notifications, since they can easily keep track of their outgoing (absolute) timestamps and compare them to the page on notification.

**We should write a client library (similar to libi2c) to implement this functionality for users, but this is left as future work for now**.

### PPC interface

Clients interact with the timer subsystem via protected procedure calls (PPCs). These PPCs are conveniently wrapped in `<sddf/timer/client.h>`. All convenience functions take the Microkit channel ID of the timer virt as a parameter (`channel`). The following functions are available:

* `int sddf_timer_set_timeout(channel, timestamp, period, *id)`: given a timestamp, set a timeout and return a timeout ID identifying the request on success. On failure, return a non-zero int. After `timestamp` seconds are reached by the timer, the client will receive a notification to wake it up. If a `period` is specified, the timeout will be automatically repeated every `period` nanoseconds, unless it is less than `SDDF_TIMER_MIN_PERIOD_NS` in which case the request is invalid. The periodic timeout will continue until cancelled.
* `uint64_t sddf_timer_time_now(channel)`: return the current time from boot in nanoseconds.
* `int sddf_timer_set_relative_timeout(channel, delay, *id)`: convenience function wrapping `set_timeout`. Set a timeout `delay` nanoseconds from the current time. Works identically otherwise. Periods not supported.
* `int sddf_timer_cancel_timeout(channel, timeout_id)`: cancel an outstanding timeout given a timeout id, if this client requested it. Returns zero on success, or a positive number if the timeout has already expired OR belongs to a different client.

## Virtualiser

The virtualiser implements a binary heap of timeouts wherein all incoming requests are stored. The virtualiser is a passive component, running on the time-slice of a requesting client (or the driver) rather than having its own scheduling context.

The binary heap sorts for the soonest timeout, and the virtualiser will notify all clients whose notifications currently have a timestamp less than the current time. When periodic timeouts expire, the virtualiser automatically adjusts their timestamp and re-inserts them, guaranteeing that periodic timeouts maintain the same timeout ID. When non-periodic timeouts pop, their timeout ID is invalidated.

The virtualiser requests a new timeout request from the driver whenever the head of the heap has a time in the future.

### Security and denial of service resistance

There are several possible ways for clients to attack the timer virt, managed as follows:

* Clients can request a periodic timeout with an extremely short period, effectively causing the timer driver to monopolise the entire system with no time expended by the client. We resist this by enforcing a minimum periodic timeout delay
* Clients can create a periodic timeout with a starting time much lower than the current time, causing the virt to send a massive storm of notifications as it tries to notify for all the periods between the starting point and now. This is handled by having the virt refuse to send periodic timeouts retroactively - it instead "fast forwards" to skip all previous periodic repeats.
* Clients can monopolise the timer heap by making lots of requests. We statically enforce a limit for the number of timeouts clients can request at once to manage this.

### Current time page

Similarly to the page mapped to clients from the virt, the virt shares a page with the driver containing the time of the most recent timer interrupt. This is an optimisation to prevent a pointless PPC to get the current time every time the driver notifies the virt. The virt uses the contents of this page to populate the page for a client, if the timeout corresponded to that client's request.

### Timeout ID allocation

We generate unique timeout IDs using a bit field containing the same number of bits as timeouts. This is something we should probably extract into a library in the future as this may be useful for generating cookies. Timeout IDs are guaranteed to be unique and impossible to reallocate until a timeout has either expired or been cancelled (if periodic or client abandons request).

## Driver

Timer drivers only ever contain a single timeout request at a time. The driver can only communicate directly with the virtualiser. The virtualiser can request timeouts or get the current time from the driver via a PPC.

### Shared time page updating

The driver updates the virt-driver timeout time page every time:
a. An interrupt fires,
b. The virt makes a PPC of any type.

This ensures that the virt always has the most recent time when the driver interacts with it.

### Common protected() function

The `protected()` function has been extracted into a common function that performs necessary sanity checking for all drivers. Drivers now must be compiled with `timer_driver_virt.c` (i will probably rename this), and simply define the following two protocol-defined functions which the protected method calls:
1. `bool set_new_timeout(uint64_t timestamp)`
2. `uint64_t get_current_time(void)`

### Common time conversion logic

Previously, every timer driver tried to do its own frequency conversion math. Unfortunately, most of them did it in ways that are either wrong, cannot run for a long enough time, or both. Given the complexity of the math required and the significant room for error in performing the integer arithmetic with a wide range of possible clock frequencies, we have added a common time conversion module for all drivers to use in `time_conv.c`.

This module uses a method heavily based on Linux's time conversion method. Rather than calculating terms like `ns = (ticks * freq) / NS_IN_S` directly, this method converts all such fractions into a multiply-and-shift operation representing the fraction more precisely for (efficient) integer arithmetic.

Rather than manually defining conversions to certain time units as needed, we instead model all jiffy-to-time conversions as a shift of frequencies. For example, rather than converting "to nanoseconds", we can instead convert the number of periods at some frequency `f_a` to the number of periods in another frequency, `f_b`. If `f_b` is 1GHz, a period is equal to exactly 1 nanosecond. This means that we can have a single robust method that handles the conversion in both directions, for all frequencies. If we say the number of periods in `f_a` is `t_a` and the number of periods in `f_b` is `t_b`, the algebra looks as follows, where we want to find `t_b` given `f_a`, f_b` and `t_a`.

$$
t_{f_b} = \frac{{t_{f_a}} \times f_b} {f_a}
$$

To avoid loss in integer division, we convert the equation into the following shape:

$$
t_{f_b} = \frac{t_{f_a} \times M}{2^{S}}
$$

Where `M` and `S` are arbitrary numbers encoding the value of `f_a` and `f_b` by effectively moving everything but `f_b`'s  factor of 2 to the numerator of the expression. In the code, we evaluate this expression trivially as

```c
uint64_t do_freq_shift(uint64_t t_a, uint64_t mult, uint64_t shift) {
     __uint128_t multiplicand = (__uint128_t)t_a * (__uint128_t)mult;
    return (uint64_t) (multiplicand >> shift);
}
```
... returning `t_b`, since we can find a division by 2 to the power of S with a left shift.

This method of conversion should guarantee about 100 years of time conversions accurately for any frequency in Hz that can be stored in 32 bits.

An iterative method is used to calculate the mult and shift.

### Common time cached time conversion logic

To make the above mult-shift operation more friendly, see `timer_common.c`, a file implementing two methods:
* `tick_to_ns_cached`,
* `ns_to_tick_cached`

These methods take in the two required frequencies and do all conversions necessary transparently. The mult and shift used for ns->ticks and ticks-> ns are cached for efficiency. Timer drivers are not forced to use this logic - they may want to use their own method if they do something complex like dynamically reprogramming the prescaler. For all ten of the existing drivers however, the caching behaviour is optimal and should be used.

