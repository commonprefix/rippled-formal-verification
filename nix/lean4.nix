# Lean4 toolchain (lean, lake), pinned by formal_verification/lean-toolchain.
#
# Unpacks the official leanprover/lean4 release instead of building from source
# (which nixpkgs' `lean4` does, in ~25 min): a release build reports the upstream
# `lean --githash`, which lake records in its build traces.
{
  lib,
  stdenv,
  fetchurl,
  zstd,
  autoPatchelfHook,
  fixDarwinDylibNames,
}:
let
  # "leanprover/lean4:vX.Y.Z" -> "X.Y.Z". Single source of truth with lake.
  version = lib.head (
    lib.splitString "\n" (
      lib.removePrefix "leanprover/lean4:v" (builtins.readFile ../formal_verification/lean-toolchain)
    )
  );

  # Bump alongside the lean-toolchain pin. A stale hash fails the build and
  # prints the correct one, so it cannot silently fetch the wrong toolchain.
  releases = {
    x86_64-linux = {
      tag = "linux";
      hash = "sha256-zrOj+ET3rr9jJF4rUcKNWw7TiULBn5PPP+vVIDAhYL0=";
    };
    aarch64-linux = {
      tag = "linux_aarch64";
      hash = "sha256-yGWAEmHHR9TxXQi+ypq8IKypB5BKu7KE3iWjf0tFWLw=";
    };
    x86_64-darwin = {
      tag = "darwin";
      hash = "sha256-TJfaEKkm2Qat8z/JmKJUakED6gzfmVzs78G6ox/twAg=";
    };
    aarch64-darwin = {
      tag = "darwin_aarch64";
      hash = "sha256-YZQvnRkH25GAIBVKUXyH+2SEHkjOuwAy/AkJ340YmgU=";
    };
  };

  inherit (stdenv.hostPlatform) system;
  release =
    releases.${system} or (throw "lean4: no release pinned for ${system}, add it to nix/lean4.nix");
in
stdenv.mkDerivation {
  pname = "lean4";
  inherit version;

  src = fetchurl {
    url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${release.tag}.tar.zst";
    inherit (release) hash;
  };

  nativeBuildInputs = [
    zstd
  ]
  ++ lib.optional stdenv.hostPlatform.isLinux autoPatchelfHook
  ++ lib.optional stdenv.hostPlatform.isDarwin fixDarwinDylibNames;

  # The release binaries name the FHS loader in PT_INTERP; autoPatchelfHook
  # retargets them at the Nix one.
  buildInputs = lib.optional stdenv.hostPlatform.isLinux stdenv.cc.cc.lib;

  # Keep the release layout as shipped: bin/ needs lib/lean/ beside it.
  installPhase = ''
    runHook preInstall
    mkdir -p $out
    mv ./* $out/
    runHook postInstall
  '';

  meta = {
    description = "Lean4 theorem prover and toolchain (official release)";
    homepage = "https://github.com/leanprover/lean4";
    license = lib.licenses.asl20;
    platforms = lib.attrNames releases;
    mainProgram = "lean";
  };
}
