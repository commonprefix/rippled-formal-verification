{
  description = "Nix related things for xrpld";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    # nixpkgs snapshot (2020-06-30) that shipped glibc 2.31 as the primary
    # version — matches the system libc on Ubuntu 20.04 LTS. Imported
    # manually (flake = false) because this revision predates nixpkgs'
    # own flake.nix.
    nixpkgs-custom-glibc = {
      url = "github:NixOS/nixpkgs/9cd98386a38891d1074fc18036b842dc4416f562";
      flake = false;
    };
    # Pinned Rust toolchains, delivered from the Nix store. Lets the Nix CI
    # image and dev shell honour the single `rust-toolchain.toml` pin (shared
    # with the rustup-based non-Nix runners) while staying hermetic — the
    # toolchain lands in the image's Nix closure and is locked by flake.lock.
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      nixpkgs,
      nixpkgs-custom-glibc,
      rust-overlay,
      ...
    }:
    let
      forEachSystem = import ./nix/utils.nix { inherit nixpkgs nixpkgs-custom-glibc rust-overlay; };
    in
    {
      devShells = forEachSystem (import ./nix/devshell.nix);
      packages = forEachSystem (
        args:
        (import ./nix/ci-env.nix args)
        // {
          # The Lean toolchain pinned by formal_verification/lean-toolchain.
          # Part of the formal-verification dev shell; exposed separately so it
          # can be built (warmed) on its own.
          lean4 = (import ./nix/lean4.nix { inherit (args) pkgs; }).toolchain;
        }
      );
      formatter = forEachSystem ({ pkgs, ... }: pkgs.nixfmt);
    };
}
