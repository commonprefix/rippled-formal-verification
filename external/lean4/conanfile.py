from pathlib import Path

from conan import ConanFile
from conan.errors import ConanInvalidConfiguration
from conan.tools.files import copy, get

# sha256-pinned Lean releases per platform (no elan installer) (bump with the lean-toolchain pin)
_SHA256 = {
    ("Macos", "x86_64"): "67002270b63c6cb12d6024fd00a38aa1e5fc9dc9b6c91cd3bd6f5aa34ed333ef",
    ("Macos", "armv8"): "55132a570e3dfc6203626944b262793c0f0f6a8230c0d09344a06ac992fac4a9",
    ("Linux", "x86_64"): "c8531faaa4a93d5a4dae0c742cbc1bd42a2993594d02f93a9d629ebf299fb2c8",
    ("Linux", "armv8"): "ffdfdbe00c975e3f31880fcb636135f6bec806d569583dcb280f5a68b6873e05",
}

RELEASE_URL = "https://github.com/leanprover/lean4/releases/download/v{version}/lean-{version}-{os_tag}{arch_suffix}.zip"


class Lean(ConanFile):
    """Lean 4 toolchain (lean, lake, headers, runtime) from the pinned leanprover/lean4 release.

    Version defaults from formal_verification/lean-toolchain, pass --version
    when exporting outside the repo layout (e.g. the CI image).
    """

    name = "lean4"
    license = "Apache-2.0"
    url = "https://github.com/leanprover/lean4"
    description = "The Lean 4 theorem prover and toolchain"
    settings = "os", "arch"

    def set_version(self):
        if self.version is None:
            toolchain = Path(
                self.recipe_folder, "..", "..", "formal_verification", "lean-toolchain"
            )
            # "leanprover/lean4:vX" -> "X"
            self.version = toolchain.read_text(encoding="utf-8").strip().split(":v")[1]

    def build(self):
        os_name, arch = str(self.settings.os), str(self.settings.arch)
        sha256 = _SHA256.get((os_name, arch))
        if sha256 is None:
            raise ConanInvalidConfiguration(f"lean4: unsupported platform {os_name}/{arch}")
        os_tag = "darwin" if os_name == "Macos" else "linux"
        arch_suffix = "_aarch64" if arch == "armv8" else ""
        url = RELEASE_URL.format(
            version=self.version, os_tag=os_tag, arch_suffix=arch_suffix
        )
        get(
            self,
            url,
            sha256=sha256,
            strip_root=True,
            keep_permissions=True,
            destination=Path(self.build_folder) / "toolchain",
        )

    def package(self):
        copy(
            self,
            "*",
            src=Path(self.build_folder) / "toolchain",
            dst=self.package_folder,
        )

    def package_info(self):
        self.cpp_info.includedirs = ["include"]
        self.cpp_info.libdirs = [str(Path("lib") / "lean")]
        self.cpp_info.libs = ["Lake", "leanshared"]  # order matters: Lake before the runtime
        self.cpp_info.bindirs = ["bin"]
        self.buildenv_info.prepend_path("PATH", str(Path(self.package_folder) / "bin"))
