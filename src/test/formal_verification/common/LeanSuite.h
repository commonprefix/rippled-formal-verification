#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>

#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <mutex>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <string_view>
#include <vector>

extern "C" void
lean_initialize_runtime_module(void);

extern "C" lean_object*
initialize_XRPL_XRPL_FFI_FFI(uint8_t builtin);

namespace xrpl::test::formal_verification {

// Per-thread RNG; beginCase reseeds it deterministically per case.
inline std::mt19937_64&
nextRng()
{
    thread_local std::mt19937_64 rng{0xBEEFCAFEDEADBEEFULL};
    return rng;
}

[[nodiscard]] inline std::string
leanErrorText(LeanError e)
{
    switch (e)
    {
        case LeanError::overflow:
            return "overflow";
        case LeanError::divByZero:
            return "divByZero";
        case LeanError::outOfRange:
            return "outOfRange";
        case LeanError::normalize1:
            return "normalize1";
        case LeanError::normalize1_5:
            return "normalize1_5";
        case LeanError::normalize2:
            return "normalize2";
        case LeanError::notComparable:
            return "notComparable";
        case LeanError::cannotConvert:
            return "cannotConvert";
        case LeanError::notLawful:
            return "notLawful";
        case LeanError::badInput:
            return "badInput";
        case LeanError::wrap:
            return "wrap";
    }
    return std::to_string(static_cast<int>(e));
}

[[nodiscard]] inline std::string
leanErrorText(std::optional<LeanError> e)
{
    return e ? leanErrorText(*e) : std::string{"none"};
}

[[nodiscard]] inline std::string
resultText(TER t)
{
    return transToken(t);
}

[[nodiscard]] inline std::string
resultText(std::int64_t v)
{
    return std::to_string(v);
}

// Base for Lean-FFI test suites. run() guards Lean init + serializes all FFI
// calls behind a mutex (Lean's runtime is single-threaded).
class LeanSuite : public beast::unit_test::Suite
{
    static std::mutex&
    leanMutex()
    {
        static std::mutex m;
        return m;
    }

    static bool
    ensureLeanInit()
    {
        static std::once_flag flag;
        static bool ok = false;
        std::call_once(flag, [] {
            lean_initialize_runtime_module();
            lean_object* res = initialize_XRPL_XRPL_FFI_FFI(1);
            if (!lean_io_result_is_ok(res))
            {
                lean_io_result_show_error(res);
                lean_dec(res);
                return;
            }
            lean_dec_ref(res);
            lean_io_mark_end_initialization();
            ok = true;
        });
        return ok;
    }

    virtual void
    runTests() = 0;

protected:
    // Pass "Suite.method" for seedRng so the per-thread RNG seed is unique
    // across suites that share method names.
    void
    beginCase(char const* name, bool seedRng = false)
    {
        testcase << name;
        if (seedRng)
            nextRng().seed(std::hash<std::string_view>{}(name));
    }

    template <typename F>
    void
    runFuzz(int iterations, F&& check)
    {
        for (int i = 0; i < iterations; ++i)
            (void)check();
    }

    // A model operation over a valid state must never be rejected as not lawful
    template <class R>
    void
    expectLawful(R const& r)
    {
        BEAST_EXPECTS(
            r.leanError != LeanError::notLawful, "model rejected the staged state as not lawful");
    }

    // Row `index` of a list must give the result the list expects; `values` prints the row.
    template <class T>
    void
    expectResult(std::size_t index, std::string const& values, T const& got, T const& expected)
    {
        BEAST_EXPECTS(
            got == expected,
            "row " + std::to_string(index) + ": " + values + ": got " + resultText(got) +
                ", expected " + resultText(expected));
    }

public:
    void
    run() final
    {
        std::lock_guard<std::mutex> lock(leanMutex());
        if (!ensureLeanInit())
        {
            fail("Lean runtime failed to initialize");
            return;
        }
        runTests();
    }
};

}  // namespace xrpl::test::formal_verification
