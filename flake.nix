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
            # mkShellNoCC, because we do not want the cc from stdenv to leak into this shell
            pkgs.mkShellNoCC rec {
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

                (symlinkJoin {
                  name = "clang-complete";
                  paths = llvm.clang-unwrapped.all;

                  # Clang searches up from the directory where it sits to find its built-in
                  # headers. The `symlinkJoin` creates a symlink to the clang binary, and that
                  # symlink is what ends up in your PATH from this shell. However, that symlink's
                  # destination, the clang binary file, still resides in its own nix store
                  # entry (`llvm.clang-unwrapped`), isolated from the header files (found in
                  # `llvm.clang-unwrapped.lib` under `lib/clang/18/include`). So when search up its
                  # parent directories, no built-in headers are found.
                  #
                  # By copying over the clang binary over the symlinks in the realisation of the
                  # `symlinkJoin`, we can fix this; now the search mechanism looks up the parent
                  # directories of the `clang` binary (which is a copy created by below command),
                  # until it finds the aforementioned `lib/clang/18/include` (where the `lib` is
                  # actually a symlink to `llvm.clang-unwrapped.lib + "/lib"`).
                  postBuild = ''
                    cp --remove-destination -- ${llvm.clang-unwrapped}/bin/* $out/bin/
                  '';
                })

                # for git-clang-format.
                llvm.libclang.python
                llvm.lld
                llvm.libllvm
              ];

              # To avoid Nix adding compiler flags that are not available on a freestanding
              # environment.
              hardeningDisable = [ "all" ];
            };
        });
    };
}
