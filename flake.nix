#
# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
{
  description = "A flake for building sDDF";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/24.05";
    zig-overlay.url = "github:mitchellh/zig-overlay";
  };

  outputs = { nixpkgs, zig-overlay, ... }:
    let
      microkit-version = "1.4.1";
      microkit-platforms = {
        aarch64-darwin = "macos-aarch64";
        x86_64-darwin = "macos-x86-64";
        x86_64-linux = "linux-x86-64";
      };

      forAllSystems = with nixpkgs.lib; genAttrs (builtins.attrNames microkit-platforms);
    in
    {
      # Shell for developing sDDF.
      # Includes dependencies for building sDDF and its
      # examples.
      devShells = forAllSystems
        (system: {
          default =
            let
              pkgs = import nixpkgs {
                inherit system;
              };

              llvm = pkgs.llvmPackages_18;
              zig = zig-overlay.packages.${system}."0.13.0";
            in
            pkgs.mkShell rec {
              name = "sddf-dev";

              microkit-platform = microkit-platforms.${system} or (throw "Unsupported system: ${system}");

              env.MICROKIT_SDK = pkgs.fetchzip {
                url = "https://github.com/seL4/microkit/releases/download/${microkit-version}/microkit-sdk-${microkit-version}-${microkit-platform}.tar.gz";
                hash = {
                  aarch64-darwin = "sha256-QMgIpQYGFeu7Rm+KNS9vijAksuW4WXf+TJnLVtto6Lw=";
                  x86_64-darwin = "sha256-9WHEVkmSEijBiVsCWRcoSBhu4TPPzItTAx/P70/7UyM=";
                  x86_64-linux = "sha256-VpljwkGAPl/vkTBFoG6j2ivD9CMy+u3TI7pwdlz+Zho=";
                }.${system} or (throw "Unsupported system: ${system}");
              };

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

              buildInputs = [
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
    };
}
