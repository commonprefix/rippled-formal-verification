# Builds the Lean4 FFI library and links it into xrpld when formal_verification is on (default OFF).

if(NOT formal_verification)
    return()
endif()

if(NOT TARGET xrpld OR NOT tests)
    message(FATAL_ERROR "formal_verification=ON requires xrpld and tests")
endif()

# The project floor is 3.16, but the model build below needs `cmake -E env
# --unset` (3.24) to keep an ambient LEAN_CC from swapping out the Lean
# toolchain's compiler. Scoped to this opt-in feature; ordinary builds are
# unaffected.
if(CMAKE_VERSION VERSION_LESS 3.24)
    message(
        FATAL_ERROR
        "formal_verification=ON requires CMake >= 3.24, found ${CMAKE_VERSION}"
    )
endif()

foreach(_var IN ITEMS LEAN4_BINDIR LEAN4_DEPS_PACKAGES)
    if(NOT ${_var})
        message(
            FATAL_ERROR
            "formal_verification=ON needs ${_var} from the Conan toolchain"
        )
    endif()
endforeach()

find_package(lean4 REQUIRED)
find_package(lean4-deps REQUIRED)

set(lean4_src ${CMAKE_SOURCE_DIR}/formal_verification)
set(lean4_model_archive ${lean4_src}/.lake/build/lib/libXRPL_XRPLModel.a)

# The lake dependency closure is checked in conanfile.py's generate(), where
# JSON is cheap to parse and the failure surfaces at `conan install` rather than
# here.
#
# The model is always built with the Conan-provided toolchain, never one found
# on PATH. lake records Lean's githash in its build traces, so a same-version
# but differently-built lean would invalidate the prebuilt mathlib and silently
# re-elaborate all of it. Taking the toolchain from the dependency graph makes
# that impossible.
set(lean4_lake ${LEAN4_BINDIR}/lake)

# Fail at configure time rather than mid-build, where this would surface as an
# opaque "cannot execute" from a custom command.
execute_process(
    COMMAND ${lean4_lake} --version
    RESULT_VARIABLE lean4_lake_result
    OUTPUT_QUIET
    ERROR_QUIET
)
if(NOT lean4_lake_result EQUAL 0)
    message(
        FATAL_ERROR
        "formal_verification: '${lean4_lake}' cannot be executed. The lean4 "
        "package ships upstream binaries that need the FHS loader "
        "/lib64/ld-linux-x86-64.so.2. On NixOS, provide it by enabling nix-ld "
        "(programs.nix-ld.enable = true); other distributions have it already."
    )
endif()

# Mount the dep packages (mathlib .olean files) so lake can resolve the model's imports.
set(lean4_lake_dir ${lean4_src}/.lake)
file(MAKE_DIRECTORY ${lean4_lake_dir})
file(REMOVE_RECURSE ${lean4_lake_dir}/packages)
file(CREATE_LINK ${LEAN4_DEPS_PACKAGES} ${lean4_lake_dir}/packages SYMBOLIC)

# Build the model archive where DEPENDS on the model sources so edits trigger a rebuild.
file(
    GLOB_RECURSE lean4_model_sources
    CONFIGURE_DEPENDS
    ${lean4_src}/XRPL/*.lean
)
add_custom_command(
    OUTPUT ${lean4_model_archive}
    # --unset=LEAN_CC: leanc invokes $LEAN_CC when set, so a developer with it
    # pointing at a system compiler would build the model's objects with a
    # different toolchain than the dependencies' were built with. Let leanc
    # self-select its bundled clang, matching how lean4-deps was produced.
    COMMAND ${CMAKE_COMMAND} -E env --unset=LEAN_CC ${lean4_lake} build XRPLModel:static
    DEPENDS ${lean4_model_sources} ${lean4_src}/lakefile.toml
    WORKING_DIRECTORY ${lean4_src}
    COMMENT "formal_verification: Lean4 model build"
    VERBATIM
)
add_custom_target(lean4_model DEPENDS ${lean4_model_archive})

# Static link into xrpld
add_dependencies(xrpld lean4_model)
target_link_libraries(
    xrpld
    ${lean4_model_archive}
    lean4-deps::lean4-deps
    lean4::lean4
)
message(STATUS "formal_verification: Lean4 linked into xrpld")
