# SPDX-License-Identifier: MPL-2.0
{
  description = "epistemic-types — Agda formalisation of standpoint-indexed epistemic / echo-like type formers";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (s: f nixpkgs.legacyPackages.${s});
    in {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          # Agda (the proofs are self-contained: --no-libraries) + just.
          packages = [ pkgs.agda pkgs.just ];
        };
      });
    };
}
