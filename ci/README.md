<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# CI

## Testing code

Each example system as part of CI is compiled and run either in a simulator (QEMU)
or on real hardware (remotely in the Trustworthy Systems lab).

On each commit and pull request, the build and simulation tests are checked.
The hardware tests do not happen unless an explicit 'hardware test' label is added
to a pull request. This is done to not overwhelm our supply of hardware.

### Builds

You can reproduce what the CI builds with:

```sh
./ci/build.py /path/to/sdk
```

You will need to provide the path to your Microkit SDK.

There are various options to speed up development, such as only compiling a particular
example or for a particular baord.

For example, if you were working on the timer example system, you might want to instead
run:
```sh
./ci/build.py /path/to/sdk --examples timer
```

You are encouraged to explore all the script's options with:
```sh
./ci/build.py --help
```

### Runtime

There are two kinds of runtime tests, simulation via QEMU and hardware tests on actual
boards.

Simulation tests can be run on your development machine but hardware tests obviously
require actual hardware.

#### Machine Queue

The below instrucitons are only for those who have access to Trustworthy Systems'
machine queue setup.

After you've run the [build script](#builds) you can run everythign with images with

TODO: show better options/running isolated example
TODO: talk about just running qemu
```sh
./ci/run.py
```

### Internals

TODO:
* talk about matrix.py
* talk about adding your own example.py script

## Style

The CI runs a style check on any changed files and new files added in each GitHub
pull request.

We use `clang-format`, following the style guide in `.clang-format`.

### Installation

On macOS: `brew install clang-format`.

On apt: `sudo apt install clang-format`.

On Nix: `nix-shell` in the root of the repository.

### Using

You can reproduce the style check by doing the following, which prints the diff
of your committed changes against the main branch.

```sh
git clang-format --diff main
```

You can also auto-format changed files by omitting the `--diff` argument.

```sh
git clang-format main
```

Omitting the branch name runs the formatter on any staged files.
