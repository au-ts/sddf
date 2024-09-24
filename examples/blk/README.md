<!--
   Copyright 2022, UNSW
   SPDX-License-Identifier: CC-BY-SA-4.0
-->
# Block example

This example is meant to show off the various operations that are possible
with block devices in sDDF.

## Building

The following platforms are supported:
* qemu_virt_aarch64

Note that this example depends on `dosfstools`.

For `apt` users: `sudo apt-get install dosfstools`.
For Homebrew users: `brew install dosfstools`.

### Make

```sh
make MICROKIT_SDK=<path/to/sdk> MICROKIT_BOARD=<board>
```

After building, the system image to load will be `build/loader.img`.

If you wish to simulate on the QEMU virt AArch64 platform, you can append `qemu` to your make command.

### Zig

You can also build this example with the Zig build system:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=<board>
```

The options for `<board>` are the same as the Makefile.

You can simulate QEMU with:
```sh
zig build -Dsdk=/path/to/sdk -Dboard=qemu_virt_aarch64 qemu
```

The final bootable image will be in `zig-out/bin/loader.img`.

## Running

The example uses a generated C header that contains bytes for an ASCII
image of the seL4 logo and some 'Lorem ipsum' text. It writes this data
to the device and then reads it back and prints out what it got back.

When running the example, you should see the following output:
```
                                                           -------
                                                           -------
           --------                                        -------             --------
       -----------------            -----       -----      -------           ----------
     ---------------------        ---- ----   ----------   -------          -----------
   -------------------------      ----  ---  -----  ----   -------        -------------
  ---------------------------     -------    -----------   -------       -----  -------
 -----------------------------       ------  -----         -------     -----    -------
--------   -------------------    ----  ---- -----  ----   -------   ------     -------
------       ------------------------- -----------  --------------------------------------
------       -----------------------------------------------------------------------------
-------     ------------------------------------------------------------------------------
 -----------------------------                                                  -------
 ----------------------------                                                   -------
   -------------------------
    -----------------------
      ------------------
          -----------


Lorem ipsum dolor sit amet, consectetur adipiscing elit. Proin ante libero, eleifend ac enim et, accumsan mollis velit. Sed a efficitur risus. Nam in purus imperdiet lorem euismod ultricies. Vestibulum dui orci, suscipit et magna a, sodales lacinia odio. Vivamus a aliquam dui. Suspendisse et nisl ornare, lacinia odio sed, malesuada nibh. Curabitur in quam vel nisi fringilla rhoncus in a risus. Integer accumsan risus elit, et porta ligula viverra eu. Aliquam luctus elit in vulputate sodales. Mauris tempor magna a tincidunt blandit. Mauris et condimentum odio. Interdum et malesuada fames ac ante ipsum primis in faucibus.

Class aptent taciti sociosqu ad litora torquent per conubia nostra, per inceptos himenaeos. Pellentesque egestas sed nisl eget commodo. Morbi lobortis mattis ex. Donec venenatis, nisi nec viverra rutrum, orci ante porta dui, quis lacinia risus nisi non mauris. Integer imperdiet arcu facilisis mi tempus consequat. Praesent risus eros, elementum id diam vitae, faucibus hendrerit dolor. Aenean posuere sit amet nulla id interdum. Pellentesque vel massa ac velit posuere mollis.

Sed scelerisque commodo porta. Ut efficitur purus et dui commodo rhoncus. Nullam in auctor lectus, eu mattis eros. Ut libero ligula, malesuada mattis arcu et, aliquet sagittis ipsum. Nullam eget bibendum nulla, vel mattis risus. In aliquam lectus non finibus lobortis. Nunc id orci eu quam mattis rutrum sed ac ante. Etiam at risus fringilla, mollis elit eu, porttitor nibh. Proin ornare turpis augue, dictum facilisis mi ultricies eu. Phasellus vitae augue et sapien faucibus imperdiet. Duis euismod posuere congue. Integer iaculis efficitur fringilla. Proin tellus ligula, molestie sit amet sagittis at, ullamcorper et sapien. Fusce aliquet ornare arcu et egestas. Pellentesque eleifend metus non mauris vestibulum, sit amet pulvinar dolor sagittis. Cras a eleifend nisi.

Pellentesque mauris libero, posuere et urna ac, euismod hendrerit leo. Nam quis lectus elit. Suspendisse lacinia ante nisi, eget rhoncus tellus ornare in. Ut convallis dapibus eros, quis egestas ante porttitor at. Pellentesque euismod justo libero, id dignissim enim lacinia vel. Morbi non eros in lorem laoreet vulputate ac in mauris. Vivamus efficitur ligula eu quam interdum, a consequat purus imperdiet. Phasellus ipsum massa, iaculis vel lorem vulputate, eleifend euismod dolor. Morbi sit amet aliquet libero, nec aliquet lorem. Praesent imperdiet lacinia orci eget finibus. Etiam sit amet porttitor turpis. Nunc
CLIENT|INFO: basic: successfully finished
```
