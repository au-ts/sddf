<!--
    Copyright 2025, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->

# Network sub-system

## lwIP

While the sDDF network protocol does not assume a particular IP stack,
all of our experimentation and development has been done with the
lwIP stack.

### Updating lwIP

The source for lwIP is currently vendored in the source for sDDF, to
update lwIP see the script `network/ipstacks/update_lwip.sh`
