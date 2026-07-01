<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Spin models

This directory contains a set of
[Spin](https://spinroot.com/spin/whatispin.html) models of each of the
networking components in the echo server system. They are written in Spin's
modelling language PROMELA. These models were created during the development of
the [signalling protocol](/docs/developing.md#signalling-protocol) which
dictates when components are required to notify their neighbours.

The signalling protocol used in the networking subsystem is optimised to
minimise the number unnecessary notifications, while the protocol itself, as
represented in the models, is proven to be deadlock free.

## Quick-start guide

This guide assumes you have installed Spin and GCC to be usable from command
line - for example, Homebrew includes such a Spin package. For a more in-depth
guide, see the [Basic Spin Manual](https://spinroot.com/spin/Man/Manual.html).

For each PROMELA model file `mymodel.pml`, use the following sequence of shell
commands to build and run a binary from command line verifying the absence of
assertion failures or deadlocks in the model by exhaustive search.

    spin -a mymodel.pml # produces pan.c
    gcc -o mybinary pan.c # produces verification binary
    ./mybinary -m10000000 # runs with specified max depth 10000000

Note, Spin's default depth limit of 10000 (used if no `-m` argument is given)
may not be enough to verify a given model by exhaustive search - if you see an
`error: max search depth too small` followed by depths that repeatedly cap out
at the (specified depth limit - 1) then the search will not be exhaustive, in
which case you'll need to try again with an increased depth limit.

At current time of writing,
- `copy/RxOnly-SetLoop.pml` and `virt_tx/TxOnly-SetLoop.pml`
  require a depth limit of 10000000
- `client/RxTx-SetLoop.pml` and `virt_rx/RxOnly-SetLoop.pml`
  require a depth limit of 100000000
- `driver/RxTx-SetLoop.pml` needs to be compiled with `gcc -DBITSTATE` and run
  also with a depth limit of 100000000. Verifying each of its RX and TX path
  separately is also possible, with each requiring a depth limit of 100000:
  - RX path: Comment out all lines and case blocks mentioning
    `ETH_TX_free`, `ETH_TX_active`, `IRQ_TX` and `HW_TX`
  - TX path: Comment out all lines and case blocks mentioning
    `ETH_RX_free`, `ETH_RX_active`, `IRQ_RX` and `HW_RX`

Exhaustive verification may take between seconds and minutes (see the comments
in each model file) and is successful if the search doesn't end prematurely
with `assertion violated (at depth ...)` or `invalid end state (at depth ...)`
and `Warning: Search not completed` - in these cases, it will also emit a
`mymodel.pml.trail` file which you can inspect using `spin -t -p mymodel.pml`.

To test this behaviour of Spin, you can introduce an `assert(false);` or a
deadlock by adding an unsatisfiable selection `if :: false -> skip; fi` - in
the latter case, inspecting the trail file with `spin -t -p` should identify an
end state where one of the processes is at the line number of mymodel.pml where
you introduced the deadlocking (unsatisfiable `if...fi`) selection statement.
