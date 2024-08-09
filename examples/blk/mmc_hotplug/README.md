# Block (mmc) Hotplugging Example

This examples demonstrates an implementation of hotplugging.

The setup is:
- One plug controller, which can send unmount/mount requests
- A client which "plays a game" and will receive unmount/mount notifications
    - The "game" involves a client which writes a block with counts full of
      0s, then 1s, then 2s, etc, and so forth, up to UINT8_MAX.
    - The game only ever considers a "safe" unplug state to be when UINT8_MAX is written, i.e. all 1s on the device, and will prevent the controller from unplugging until before then.

- (TODO) Another client which tries to run an unmount/mount command when its not privileged.

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

It should produce the following output:

```
// TODO
```

If the SD card is yanked out without unmounting, one might see an output as below:

```bash
$ hexdump -C -n 512 /dev/mmcblk0p3
00000000  f3 f3 f3 f3 f3 f3 f3 f3  f3 f3 f3 f3 f3 f3 f3 f3  |................|
*
00000200
```

If it is safely unmounted, the output should be:

```bash
$ hexdump -C -n 512 /dev/mmcblk0p3
00000000  ff ff ff ff ff ff ff ff  ff ff ff ff ff ff ff ff  |................|
*
00000200
```
