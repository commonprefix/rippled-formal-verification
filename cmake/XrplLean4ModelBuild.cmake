# Runs `lake build XRPLModel:static` with LEAN_CC removed from the environment.
# Invoked via `cmake -P` from the custom command in XrplLean4.cmake; expects
# LEAN4_LAKE and LEAN4_SRC on the command line.
#
# leanc invokes $LEAN_CC when set, so a developer with it pointing at a system
# compiler would build the model's objects with a different toolchain than
# lean4-deps' were built with. The variable has to be *removed* rather than
# emptied: lake fails outright on an empty value ("external command '' exited
# with code 255"), which rules out the one-line `cmake -E env LEAN_CC=`.
#
# `cmake -E env --unset=LEAN_CC` expresses this directly but needs CMake 3.24,
# above the project's 3.16 floor, so the unset happens here in script mode.

unset(ENV{LEAN_CC})

execute_process(
    COMMAND ${LEAN4_LAKE} build XRPLModel:static
    WORKING_DIRECTORY ${LEAN4_SRC}
    RESULT_VARIABLE lean4_model_result
)
if(NOT lean4_model_result EQUAL 0)
    message(
        FATAL_ERROR
        "formal_verification: Lean4 model build failed (${lean4_model_result})"
    )
endif()
