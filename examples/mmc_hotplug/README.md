<!--
    Copyright 2024, UNSW
    SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Block (mmc) Hotplugging Example

This examples demonstrates an implementation of hotplugging.

The setup is:
- One plug controller, which can send insert/eject requests to the block virtualiser.
- A client which "plays a game" and will receive "pending eject" notifications from the controller
    - The "game" involves a client which writes a block with counts full of
      0s, then 1s, then 2s, etc, and so forth, up to UINT8_MAX.
    - The game only ever considers a "safe" unplug state to be when UINT8_MAX is written, i.e. all 1s on the device, and will prevent the controller from unplugging until before then.


## Building
### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board> MICROKIT_CONFIG=<debug/release>
```

Currently the options for `MICROKIT_BOARD` are:

* maaxboard
* imx8mm_evk

## Running

The produced `build/loader.img` can then be loaded from U-Boot.

It should produce something like the following output. Note that the text might appear somewhat scrambled.

```bash
Hello from plug controller
GAME: Hello!
PLUG: Storage is now ready
GAME: Storage ready!
GAME: playing...
GAME: Enqueued a playthrough
GAME: Finished a playthrough
GAME: Enqueued a playthrough
# at this point the card was removed (checkpoint #1)
GAME: Received 1 or more non-successful queue response...
GAME: -> 1st: status: 2, count: 1, id: 288
GAME: Errors encountered, stopping play.
PLUG: Storage is now not ready
GAME: Storage is no longer ready
# the card is then reinserted
PLUG: Storage is now ready
GAME: Storage ready!
GAME: playing...
GAME: Enqueued a playthrough
# the '[' key is pressed, triggerring a safe eject
PLUG: Notifying clients of pending EJECT...
GAME: Hotplug notify: pending eject...: 1
GAME: Finished a playthrough
PLUG: Safe to eject from client: 0
PLUG: All clients responded... ejecting
PLUG: -> response: 0
PLUG: Storage is now not ready
GAME: Storage is no longer ready
```

At checkpoint #1 above, during an unsafe ejection, the card should read something like:

```bash
$ hexdump -C -n 512 /dev/mmcblk0p3
00000000  bb bb bb bb bb bb bb bb  bb bb bb bb bb bb bb bb  |................|
*
00000200
```

If it is safely ejected (as at checkpoint #2), the output should be:

```bash
$ hexdump -C -n 512 /dev/mmcblk0p3
00000000  ff ff ff ff ff ff ff ff  ff ff ff ff ff ff ff ff  |................|
*
00000200
```
