#
# Copyright 2026, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#

{
  stdenv,
  fetchzip,
  pancakeVersion ? 3440,
}:

stdenv.mkDerivation (rec {
  pname = "pancake";
  version = "3440";

  src =
    let
      hostArch = stdenv.hostPlatform.qemuArch;

      cakemlPlatformNameAndHash =
        {
          aarch64 = {
            arch = "arm8-64";
            hash = "sha256-1xVVQFunYSxMvGkmApWLfZ+s+hvQ2B5a7sJsoE1K5Qg=";
          };
          x86_64 = {
            arch = "x64-64";
            hash = "sha256-uNt5HhpBixfEItqdfWuDxt/RKq2kySyh7Fbk08tmSx4=";
          };
        }
        .${hostArch} or (throw "Unsupported architecture: ${hostArch}");
    in
    fetchzip {
      url = "https://cakeml.org/regression/artefacts/${toString pancakeVersion}/cake-${cakemlPlatformNameAndHash.arch}.tar.gz";
      hash = cakemlPlatformNameAndHash.hash;
    };

  buildPhase = ''
    runHook preBuild

    make

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    mkdir -p $out/bin
    cp cake $out/bin/

    runHook postInstall
  '';
})
