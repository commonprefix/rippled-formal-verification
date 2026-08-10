# Lean 4 toolchain and the extras the formal-verification build needs
# (see docs/formal-verification/README.md). Consumed only by the
# `formal-verification` dev shell in devshell.nix, so the regular shells and the
# CI environment don't pull the Lean toolchain into their closure.
{ pkgs }:
let
  inherit (pkgs) lib stdenv;

  # Single source of truth for the Lean version: the pin that lake and the Conan
  # recipes (external/lean4, external/lean4-deps) already read.
  # "leanprover/lean4:v4.28.0" -> "4.28.0"
  leanVersion = lib.removeSuffix "\n" (
    lib.last (lib.splitString ":v" (builtins.readFile ../formal_verification/lean-toolchain))
  );

  # The official release archives, per platform. These are sha256 sums of the
  # *archives*, identical to the ones external/lean4/conanfile.py pins — both
  # fetch the same URL, so bump `_SHA256` there and this table together when the
  # lean-toolchain pin moves.
  releases = {
    x86_64-linux = {
      tag = "linux";
      sha256 = "b02b74bb23e93e5b05f03f51ad06274814337d107718a02b6f89dc4db1387416";
    };
    aarch64-linux = {
      tag = "linux_aarch64";
      sha256 = "c608141afb645c7faa3845cc5dc503890ae329a82359f9bf37358d1fab499f81";
    };
    x86_64-darwin = {
      tag = "darwin";
      sha256 = "47010e6040ab2441dc96c1d9a3aca1721576fdbe4da566d938b29a26502fd378";
    };
    aarch64-darwin = {
      tag = "darwin_aarch64";
      sha256 = "d63a34d12978b035f871c8448d7243eb16711b8f5b27d7e9b093a210c1117e8d";
    };
  };
  release =
    releases.${stdenv.hostPlatform.system}
      or (throw "lean4: unsupported platform ${stdenv.hostPlatform.system}");

  # Libraries the prebuilt toolchain expects from the system. Its own bundled
  # libc++ / libgmp / libuv live under lib/ and are found there, so this only
  # needs to cover the base ones.
  systemLibs = [
    stdenv.cc.cc.lib
    pkgs.gmp
    pkgs.libuv
    pkgs.zlib
  ];

  # The pinned Lean release, unpacked from the upstream binary archive. It is not
  # built from source and not relocatable: the binaries reference the system ELF
  # loader, which NixOS doesn't have, so autoPatchelf retargets them at the Nix
  # store. Using the release (rather than nixpkgs' `lean4`, which tracks a
  # different version) is what makes the prebuilt mathlib olean cache usable:
  # lake only accepts a cache built by the exact toolchain in lean-toolchain.
  toolchain = stdenv.mkDerivation {
    pname = "lean4";
    version = leanVersion;

    src = pkgs.fetchurl {
      url = "https://github.com/leanprover/lean4/releases/download/v${leanVersion}/lean-${leanVersion}-${release.tag}.zip";
      inherit (release) sha256;
    };

    nativeBuildInputs = [ pkgs.unzip ] ++ lib.optional stdenv.isLinux pkgs.autoPatchelfHook;
    buildInputs = systemLibs;

    dontConfigure = true;
    dontBuild = true;
    # Nothing to gain from stripping a binary release, and lean's own tooling is
    # the only consumer of these binaries.
    dontStrip = true;

    # lean, lake and leanc resolve their sysroot relative to argv[0], so the
    # release layout has to be preserved as shipped.
    installPhase = ''
      runHook preInstall
      mkdir -p "$out"
      cp -R . "$out"
      runHook postInstall
    '';

    meta = {
      description = "Lean 4 toolchain pinned by formal_verification/lean-toolchain";
      homepage = "https://lean-lang.org";
      license = lib.licenses.asl20;
      platforms = builtins.attrNames releases;
    };
  };

  # xrpld links libleanshared.so, whose RUNPATH doesn't cover its own transitive
  # libLake_shared.so, so the built binary needs the runtime on the search path.
  runtimeLibraryPathHook =
    if stdenv.isDarwin then
      ''
        export DYLD_LIBRARY_PATH="${toolchain}/lib/lean''${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
      ''
    else
      ''
        export LD_LIBRARY_PATH="${toolchain}/lib/lean''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
      '';
in
{
  inherit toolchain leanVersion;

  packages = [
    toolchain
  ]
  ++ (with pkgs; [
    # `lake exe cache get` bootstraps leantar by unpacking a .tar.gz, then
    # unpacks the mathlib cache itself (.tar.zst).
    gnutar
    gzip
    zstd
  ]);

  # Plain env vars for the shell; anything needing append semantics is in
  # shellHook below.
  shellEnv = {
    # lake compiles the model's generated C through leanc, which defaults to a
    # compiler path baked into the release. Use the shell's compiler instead.
    LEAN_CC = "${stdenv.cc}/bin/cc";
    # Makes the Conan lean4 recipe (external/lean4) link this toolchain instead
    # of downloading the release, whose binaries don't run on NixOS unpatched.
    # One Lean install, used by lake here and by conan/cmake for the FFI build.
    XRPL_LEAN4_DIR = "${toolchain}";
  };

  shellHook = ''
    # Building lean4-deps links mathlib's `cache` executable against the Lean
    # runtime's bundled -lc++ -lc++abi -lgmp -luv, which exist only here.
    export LIBRARY_PATH="${toolchain}/lib''${LIBRARY_PATH:+:$LIBRARY_PATH}"
  ''
  + runtimeLibraryPathHook
  + lib.optionalString stdenv.isLinux ''
    # Not needed for the toolchain above (XRPL_LEAN4_DIR keeps Conan on it), but
    # it lets any other prebuilt binary that ends up in the Conan cache — such as
    # a lean4 package created before that variable existed — run through nix-ld.
    export NIX_LD="$(cat ${stdenv.cc}/nix-support/dynamic-linker)"
    export NIX_LD_LIBRARY_PATH="${lib.makeLibraryPath (systemLibs ++ [ pkgs.glibc ])}"
  '';
}
