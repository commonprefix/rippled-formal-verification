#pragma once

#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/ffi/LeanObjectFFI.h>

#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/TER.h>

#include <lean/lean.h>

#include <algorithm>
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

    // Around its cusp a row must reach one of the `across` verdicts next to another one, or it
    // missed the cusp. `describe(cusp)` labels the row in the failure message.
    template <class Cusp>
    void
    expectCrossed(Cusp const& cusp, std::set<TER> const& seen, std::vector<TER> const& across)
    {
        bool const crossed =
            seen.size() > 1 && std::ranges::any_of(across, [&](TER t) { return seen.contains(t); });
        std::string verdicts;
        for (TER const t : seen)
            verdicts += " " + transToken(t);
        BEAST_EXPECTS(
            crossed,
            describe(cusp) + ": the row never crossed to " + transToken(across.front()) + ", saw" +
                (seen.empty() ? std::string{" nothing"} : verdicts));
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
