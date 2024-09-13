<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# CI

## Building examples

Right now we only have build-time checks for all examples under `examples/`.

This is a check that runs on each commit and pull request made to the repository.
This check is required to pass for merging a pull request.

You can reproduce what the CI runs with:
```sh
./ci/examples.sh /path/to/sdk
```

You will need to provide the path to your Microkit SDK.

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
