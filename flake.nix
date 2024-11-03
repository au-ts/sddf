#
# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
{
  description = "A flake for building sDDF";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/24.05";
    utils.url = "github:numtide/flake-utils";
    zig-overlay.url = "github:mitchellh/zig-overlay";
  };

  outputs = { self, nixpkgs, zig-overlay, ... }@inputs: inputs.utils.lib.eachSystem [
    "x86_64-linux"
    "aarch64-linux"
    "x86_64-darwin"
    "aarch64-darwin"
  ]
    (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };

        llvm = pkgs.llvmPackages_18;
        zig = zig-overlay.packages.${system}."0.13.0";
      in
      {
        # Shell for developing sDDF.
        # Includes dependencies for building sDDF and its
        # examples.
        devShells.default = pkgs.mkShell rec {
          name = "dev";

          nativeBuildInputs = with pkgs; [
            pkgsCross.aarch64-embedded.stdenv.cc.bintools
            pkgsCross.aarch64-embedded.stdenv.cc
            zig
            qemu
            gnumake
            dosfstools
            imagemagick
            # for git-clang-format.
            llvm.libclang.python
          ];

          buildInputs = with pkgs; [
            llvm.clang
            llvm.lld
            llvm.libllvm
          ];

          # To avoid compile errors since Nix adds extra arguments that are not used
          # by us.
          env.NIX_CFLAGS_COMPILE = "-Wno-unused-command-line-argument";
          # To avoid Nix adding compiler flags that are not available on a freestanding
          # environment.
          hardeningDisable = [ "all" ];
        };
      });
}
