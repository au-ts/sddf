<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# CI

## Testing code

Each example system as part of CI is compiled and run either in a simulator
(QEMU) or on real hardware (remotely in the Trustworthy Systems lab).

On each commit and pull request, the build and simulation tests are checked. The
hardware tests do not happen unless an explicit 'hardware test' label is added
to a pull request. This is done to not overwhelm our supply of hardware.

The scripts to test sDDF live in the `ci/` directory, however the general
infrastructure lives in a [separate repository](https://github.com/au-ts/systems-ci).

### Accessing Log Artifacts

As GitHub's log viewer performs terribly when the log files are large enough, we
publish archived copies on the [trustworthy.systems
website](https://trustworthy.systems/github/ci-artifacts/). Both the raw log
files, built images, and pre-rendered HTML logs are available. The archive is
updated on an hourly basis.

### Setup

Install the `ts_ci` library from `systems-ci`.

```sh
$ pip install git+https://github.com/au-ts/systems-ci#subdirectory=ts_ci
```

### Builds

You can reproduce what the CI builds with:

```sh
./ci/build.py /path/to/sdk
```

You will need to provide the path to your Microkit SDK.

There are various options to speed up development, such as only compiling a
particular example or for a particular board.

For example, if you were working on the timer example system, you might want to
instead run:
```sh
./ci/build.py /path/to/sdk --examples timer
```

You are encouraged to explore all the script's options with:
```sh
./ci/build.py --help
```

Take a look at the `--override-image` option to the individual example's script
if you are doing development of a certain example.

### Runtime

There are two kinds of runtime tests, simulation via QEMU and hardware tests on
actual boards.

Simulation tests can be run on your development machine but hardware tests
obviously require actual hardware.

After you've run the [build script](#builds) you can run everything with images
with:
```sh
./ci/run.py
```

There are various options, such as running only a specific example:
```sh
./ci/run.py --example <EXAMPLE>
```

All the options can be found with:
```sh
./ci/run.py --help
```

For developing specific examples, the example's script can be invoked directly,
which gives more options for filtering what gets run and how.

```sh
./ci/examples/blk.py --help
```

One useful option is `--override-image` which allows you to do testing of a
certain example repeatedly, for debugging:

```sh
$ make MICROKIT_BOARD=maaxboard

[[ builds ]]

$ ../../ci/examples/blk.py --override-image build/loader.img --single --boards maaxboard
CI|INFO: Running blk on maaxboard (custom, built with custom)
CI|INFO: Acquired lock: maaxboard1 LOCKED juliab 2025-10-02 12:04:24.699846598 +1000 au_ts_ci (running locally)

[[ test runs ]]

CI|INFO: Released lock: maaxboard1 FREE
CI|INFO: Test passed
CI|INFO: Finished running blk on maaxboard (custom, built with custom)
==== Passing ====
 - maaxboard: custom/custom
==== Failed =====
   (none)
```

#### Running with QEMU

If you do not have access to hardware, you can run all the simulation tests with
QEMU:
```sh
./ci/run.py --only-qemu
```

#### Adding a new test

Each test file needs to export a `TEST_CASES` variable. This is an array of
subclasses of `ts_ci.TestCase` (specifically, `common.TestConfig`) that specifies
the test cases which we are to run. We provide a `matrix.py` abstraction
`matrix.generate_example_test_cases` which can generate the list of test cases
from central information in the matrix.py.

To write a test, one needs to write a `test_fn`, and optionally, a `backend_fn`.

 -  `test_fn` is an `async def test(backend: HardwareBackend, test_config: common.TestConfig):`
    that is expected to send input and output to the example under test. It can raise
    `TestFailureException` to indicate a failure; and the helper functions
    `wait_for_output` and `expect_output` will do.

 -  `backend_fn` is optional and allows one to add extra arguments to either
    `MachineQueueBackend` or `QemuBackend` for example-specific hardware requirements.
    If you have no special requirements, pass `backend_fn=common.backend_fn`.

 -  `no_output_timeout_s` is usually left as the default `matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S`
    and is used to specify a timeout that occurs if there has been no output from
    the example under test: this is useful to catch serial hangs (etc) without
    waiting for a long timeout.

For details about the internals of `ts_ci`, please see the [systems-ci repository](
https://github.com/au-ts/systems-ci/tree/main/ts_ci).

Creating a test involves creating a Python file in the `ci/examples` folder,
and adding the relevant entries to the `matrix.py` file.

```py
# serial.py
from ts_ci import (
    expect_output,
    send_input,
    wait_for_output,
    HardwareBackend,
)

async def test(backend: HardwareBackend, test_config: common.TestConfig):
    async with asyncio.timeout(10):
        await wait_for_output(backend, b"Hello World!\n")
        await send_input(backend, b"Good morning!\r\n")
        await expect_output(backend, b"1234567890")

# export
TEST_CASES = matrix.generate_example_test_cases(
    "serial",
    matrix.EXAMPLES["serial"],
    test_fn=test,
    backend_fn=common.backend_fn,
    no_output_timeout_s=matrix.NO_OUTPUT_DEFAULT_TIMEOUT_S,
)

if __name__ == "__main__":
    common.run_tests(TEST_CASES)
```

The example matrix includes an array of configs, build systems, and boards,
and has a "tests_exclude" key that allows you to exclude certain sets of the
config from being run in tests.

```py
# matrix.py

EXAMPLES: dict[str, _ExampleMatrixType] = {
   "serial": {
        "configs": ["debug", "release"],
        "build_systems": ["make", "zig"],
        "boards": [
            "maaxboard",
            "qemu_virt_aarch64",
            "qemu_virt_riscv64",
            "x86_64_generic",
        ],
        "tests_exclude": [
            # anything with config=release is not tested
            { "config": "release" },
            # any zig builds for the maaxboard are not tested, but still built.
            { "board": "maaxboard", "build_system": "zig" },
        ],
    },

```

## Style

The CI runs a style check on any changed files and new files added in each
GitHub pull request.

### C code

We use `clang-format`, following the style guide in `.clang-format` for C code.

#### Installation

On macOS: `brew install clang-format`.

On apt: `sudo apt install clang-format`.

On Nix: `nix develop` in the root of the repository.

#### Using

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

### Python code

For helper scripts and the metaprograms (`meta.py`) which are written in Python,
we use [black](https://black.readthedocs.io/en/stable/).

Running `black . --required-version 25` in the root of the repository or on a
specific directory/file will run the Python style check.

Note that currently we target the 2025 styling of black.
