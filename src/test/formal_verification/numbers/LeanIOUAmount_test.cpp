#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/protocol/IOUAmountFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberHelpers.h>
#include <test/formal_verification/numbers/helpers/NumberSweepCases.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/IOUAmount.h>

#include <cstdint>
#include <initializer_list>
#include <limits>
#include <random>
#include <sstream>
#include <stdexcept>

// Lean IOUAmount ops (exported by xrpl-lean4/XRPL/IOUAmount/FFI.lean).
extern "C" {
lean_object*
lean_iou_amount_build(int64_t mantissa, int64_t exponent);
lean_object*
lean_iou_of_mantissa_exp(int64_t, int64_t, uint8_t);
lean_object*
lean_iou_of_number(lean_object*, uint8_t);
lean_object*
lean_iou_to_number(lean_object*, uint8_t);
lean_object*
lean_iou_add(lean_object*, lean_object*, uint8_t);
}

namespace xrpl::test {

using namespace formal_verification;
using namespace formal_verification::number_sweep;

class LeanIOUAmount_test : public LeanSuite
{
    static std::string
    fmtIOU(int64_t m, int64_t e)
    {
        std::stringstream ss;
        ss << m << "e" << e;
        return ss.str();
    }

    static std::string
    fmtIOU(IOUAmount const& a)
    {
        return fmtIOU(a.mantissa(), a.exponent());
    }

    static std::string
    fmtIOU(LeanIOUResult const& r)
    {
        if (!r.ok)
            return "<err>";
        return fmtIOU(r.mantissa, r.exponent);
    }

    // Compare a Lean IOUAmount result to a C++ outcome (which may throw).
    bool
    checkIOUResult(
        std::string const& label,
        LeanIOUResult const& lean,
        IOUAmount const& cpp,
        bool cppThrew)
    {
        if (lean.ok == cppThrew)
        {
            std::stringstream ss;
            ss << label << ": error mismatch (lean." << (lean.ok ? "ok" : "error") << ", cpp."
               << (cppThrew ? "threw" : "ok") << ")";
            fail(ss.str());
            return false;
        }
        if (!lean.ok)
        {
            pass();
            return true;
        }
        if (lean.mantissa != cpp.mantissa() || lean.exponent != cpp.exponent())
        {
            std::stringstream ss;
            ss << label << ": result mismatch lean=" << fmtIOU(lean) << " cpp=" << fmtIOU(cpp);
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    // ofMantissaExp ↔ IOUAmount{m, e}.
    bool
    checkOfMantissaExp(int64_t m, int64_t e, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        auto lean = IOUAmountFFI::fromExcept(lean_iou_of_mantissa_exp(m, e, toLeanMode(mode)));
        IOUAmount cpp;
        bool cppThrew = false;
        try
        {
            cpp = IOUAmount{m, static_cast<int>(e)};
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        return checkIOUResult("ofMantissaExp(" + fmtIOU(m, e) + ")", lean, cpp, cppThrew);
    }

    // ofNumber ↔ IOUAmount{Number{...}}.
    bool
    checkOfNumber(NumberPair const& p, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        auto lean = IOUAmountFFI::fromExcept(lean_iou_of_number(
            lean_number_build(
                p.leanNum.negative, p.leanNum.mantissa, static_cast<int64_t>(p.leanNum.exponent)),
            toLeanMode(mode)));
        IOUAmount cpp;
        bool cppThrew = false;
        try
        {
            cpp = IOUAmount{p.cppNum};
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        std::stringstream label;
        label << "ofNumber(" << (p.leanNum.negative ? "-" : "+") << p.leanNum.mantissa << "e"
              << p.cppNum.exponent() << ")";
        return checkIOUResult(label.str(), lean, cpp, cppThrew);
    }

    // toNumber ↔ static_cast<Number>(IOUAmount).
    bool
    checkToNumber(IOUAmountPair const& p, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        auto lean = NumberFFI::fromExcept(lean_iou_to_number(
            lean_iou_amount_build(p.leanIou.mantissa, p.leanIou.exponent), toLeanMode(mode)));
        Number cpp;
        bool cppThrew = false;
        try
        {
            cpp = static_cast<Number>(p.cppIou);
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        std::stringstream label;
        label << "toNumber(" << fmtIOU(p.cppIou) << ")";
        if (lean.ok == cppThrew)
        {
            std::stringstream ss;
            ss << label.str() << ": error mismatch (lean." << (lean.ok ? "ok" : "error") << ", cpp."
               << (cppThrew ? "threw" : "ok") << ")";
            fail(ss.str());
            return false;
        }
        if (!lean.ok)
        {
            pass();
            return true;
        }
        if (!fieldsEqual(lean, cpp))
        {
            std::stringstream ss;
            ss << label.str() << ": result mismatch lean=" << format(lean)
               << " cpp=" << format(cpp);
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    // Round-trip IOUAmount → Number → IOUAmount must be identity.
    bool
    checkRoundTripIOUNumberIOU(int64_t m, int64_t e, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        // First normalize via Lean ofMantissaExp so we test the canonical form.
        auto canonical = IOUAmountFFI::fromExcept(lean_iou_of_mantissa_exp(m, e, toLeanMode(mode)));
        bool ok1 = BEAST_EXPECT(canonical.ok);
        if (!ok1)
            return false;
        // toNumber
        auto asNum = NumberFFI::fromExcept(lean_iou_to_number(
            lean_iou_amount_build(canonical.mantissa, canonical.exponent), toLeanMode(mode)));
        bool ok2 = BEAST_EXPECT(asNum.ok);
        if (!ok2)
            return false;
        // back via ofNumber
        auto back = IOUAmountFFI::fromExcept(lean_iou_of_number(
            lean_number_build(asNum.negative, asNum.mantissa, static_cast<int64_t>(asNum.exponent)),
            toLeanMode(mode)));
        bool ok3 = BEAST_EXPECT(back.ok);
        if (!ok3)
            return false;
        bool eq = (back.mantissa == canonical.mantissa) && (back.exponent == canonical.exponent);
        if (!eq)
        {
            std::stringstream ss;
            ss << "round_trip(" << fmtIOU(m, e) << "): canonical=" << fmtIOU(canonical)
               << " back=" << fmtIOU(back);
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    bool
    checkAdd(IOUAmountPair const& a, IOUAmountPair const& b, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        auto lean = IOUAmountFFI::fromExcept(lean_iou_add(
            lean_iou_amount_build(a.leanIou.mantissa, a.leanIou.exponent),
            lean_iou_amount_build(b.leanIou.mantissa, b.leanIou.exponent),
            toLeanMode(mode)));
        IOUAmount cpp;
        bool cppThrew = false;
        try
        {
            cpp = a.cppIou + b.cppIou;
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        return checkIOUResult(
            "add(" + fmtIOU(a.cppIou) + "," + fmtIOU(b.cppIou) + ")", lean, cpp, cppThrew);
    }

    static int64_t
    randomMantissa(std::mt19937_64& rng, uint64_t magnitudeMin, uint64_t magnitudeMax)
    {
        std::uniform_int_distribution<uint64_t> dist(magnitudeMin, magnitudeMax);
        std::bernoulli_distribution sign(0.5);
        uint64_t mag = dist(rng);
        return sign(rng) ? -static_cast<int64_t>(mag) : static_cast<int64_t>(mag);
    }

    static int64_t
    randomExponent(std::mt19937_64& rng, int min, int max)
    {
        std::uniform_int_distribution<int> dist(min, max);
        return static_cast<int64_t>(dist(rng));
    }

public:
    void
    test_known_construction()
    {
        beginCase("LeanIOUAmount.known_construction");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);

        constexpr int64_t kMinValue = static_cast<int64_t>(STAmount::kMinValue);  // 10^15
        constexpr int64_t kMaxValue = static_cast<int64_t>(STAmount::kMaxValue);  // 10^16 - 1
        constexpr int eMin = STAmount::kMinOffset;
        constexpr int eMax = STAmount::kMaxOffset;

        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            // Zero handling (canonical IOU zero: m=0, e=-100).
            checkOfMantissaExp(0, 0, mode);
            checkOfMantissaExp(0, 5, mode);
            checkOfMantissaExp(0, -100, mode);

            // Already-normalized inputs at boundary.
            checkOfMantissaExp(kMinValue, 0, mode);
            checkOfMantissaExp(kMaxValue, 0, mode);
            checkOfMantissaExp(-kMinValue, 0, mode);
            checkOfMantissaExp(-kMaxValue, 0, mode);

            // Below kMinValue → multiplied up.
            checkOfMantissaExp(1, 0, mode);
            checkOfMantissaExp(-1, 0, mode);
            checkOfMantissaExp(kMinValue - 1, 0, mode);

            // Above kMaxValue → divided down.
            checkOfMantissaExp(kMaxValue + 1, 0, mode);
            checkOfMantissaExp(kMaxValue * 9, 0, mode);

            // Exponent boundaries — canonical mantissa at the offset corners.
            checkOfMantissaExp(kMinValue, eMin, mode);
            checkOfMantissaExp(kMinValue, eMax, mode);
            checkOfMantissaExp(kMaxValue, eMin, mode);
            checkOfMantissaExp(kMaxValue, eMax, mode);

            // ofNumber happy path: in-range Number maps to a normalized IOU.
            checkOfNumber(makeNumberPair(false, 1'000'000'000'000'000'000ULL, 0), mode);
            checkOfNumber(makeNumberPair(true, 1'000'000'000'000'000'000ULL, 0), mode);
            checkOfNumber(makeNumberPair(false, 5'000'000'000'000'000'000ULL, -3), mode);
            checkOfNumber(makeNumberPair(false, Number::minMantissa(), eMin), mode);
            checkOfNumber(makeNumberPair(false, Number::kMaxRep, eMax), mode);

            // toNumber on canonical IOUAmount values.
            checkToNumber(makeIOUAmountPair(kMinValue, 0), mode);
            checkToNumber(makeIOUAmountPair(kMaxValue, 0), mode);
            checkToNumber(makeIOUAmountPair(-kMinValue, 0), mode);
            checkToNumber(makeIOUAmountPair(-kMaxValue, 0), mode);
            checkToNumber(makeIOUAmountPair(kMinValue, eMin), mode);
            checkToNumber(makeIOUAmountPair(kMaxValue, eMax), mode);
            // toNumber on IOU zero (m=0, e=-100): mantissa-only equality.
            checkToNumber(makeIOUAmountPair(0, -100), mode);

            // Round-trip IOU -> Number -> IOU on canonical values.
            checkRoundTripIOUNumberIOU(kMinValue, 0, mode);
            checkRoundTripIOUNumberIOU(kMaxValue, 0, mode);
            checkRoundTripIOUNumberIOU(-kMaxValue, 5, mode);
            checkRoundTripIOUNumberIOU(kMinValue, -50, mode);
            checkRoundTripIOUNumberIOU(kMaxValue, eMax, mode);
            checkRoundTripIOUNumberIOU(-kMinValue, eMin, mode);
        }
    }

    void
    test_fuzz_construction()
    {
        beginCase("LeanIOUAmount.fuzz_construction", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(20'000, [&] {
                int64_t m = randomMantissa(rng, 0, std::numeric_limits<int64_t>::max());
                int64_t e = randomExponent(rng, -120, 100);
                return checkOfMantissaExp(m, e, mode);
            });
        }
    }

    void
    test_fuzz_conversion()
    {
        beginCase("LeanIOUAmount.fuzz_conversion", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(20'000, [&] { return checkToNumber(randomIOUAmountPair(rng), mode); });
        }
    }

    void
    test_known_arithmetic()
    {
        beginCase("LeanIOUAmount.known_arithmetic");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);

        constexpr int64_t kMinValue = static_cast<int64_t>(STAmount::kMinValue);
        constexpr int64_t kMaxValue = static_cast<int64_t>(STAmount::kMaxValue);

        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            // add: identity with zero.
            checkAdd(makeIOUAmountPair(kMinValue, 0), makeIOUAmountPair(0, -100), mode);
            checkAdd(makeIOUAmountPair(0, -100), makeIOUAmountPair(kMinValue, 0), mode);
            checkAdd(makeIOUAmountPair(0, -100), makeIOUAmountPair(0, -100), mode);

            // add: exact cancellation (a + (-a) = 0).
            checkAdd(makeIOUAmountPair(kMinValue, 0), makeIOUAmountPair(-kMinValue, 0), mode);
            checkAdd(makeIOUAmountPair(kMaxValue, 50), makeIOUAmountPair(-kMaxValue, 50), mode);

            // add: same-sign accumulation.
            checkAdd(makeIOUAmountPair(kMinValue, 0), makeIOUAmountPair(kMinValue, 0), mode);
            checkAdd(
                makeIOUAmountPair(5'000'000'000'000'000LL, 0),
                makeIOUAmountPair(5'000'000'000'000'000LL, 0),
                mode);

            // add: mixed-sign, partial cancellation.
            checkAdd(makeIOUAmountPair(kMaxValue, 0), makeIOUAmountPair(-kMinValue, 0), mode);
            checkAdd(makeIOUAmountPair(-kMaxValue, 0), makeIOUAmountPair(kMinValue, 0), mode);

            // add: differing exponents (shift normalization, in-range).
            checkAdd(makeIOUAmountPair(kMinValue, 0), makeIOUAmountPair(kMinValue, 5), mode);
        }
    }

    void
    test_fuzz_arithmetic()
    {
        beginCase("LeanIOUAmount.fuzz_arithmetic", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(20'000, [&] {
                auto a = randomIOUAmountPair(rng);
                auto b = randomIOUAmountPair(rng);
                return checkAdd(a, b, mode);
            });
        }
    }

    void
    test_extreme_values()
    {
        beginCase("LeanIOUAmount.extreme_values");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);

        constexpr int64_t kMin = static_cast<int64_t>(STAmount::kMinValue);
        constexpr int64_t kMax = static_cast<int64_t>(STAmount::kMaxValue);
        constexpr int eMax = STAmount::kMaxOffset;
        constexpr int eMin = STAmount::kMinOffset;

        // Largest and smallest nonzero representable magnitudes, both signs.
        auto const posMax = makeIOUAmountPair(kMax, eMax);
        auto const negMax = makeIOUAmountPair(-kMax, eMax);
        auto const posMin = makeIOUAmountPair(kMin, eMin);
        auto const negMin = makeIOUAmountPair(-kMin, eMin);

        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};

            // ofMantissaExp underflow path — exp shifts below kMinOffset → zero.
            checkOfMantissaExp(1, -110, mode);
            checkOfMantissaExp(10, -110, mode);
            // ofMantissaExp overflow path — exp shifts above kMaxOffset → error.
            checkOfMantissaExp(kMax, eMax + 1, mode);
            checkOfMantissaExp(kMin, eMax + 1, mode);
            // ofNumber overflow / underflow.
            checkOfNumber(makeNumberPair(false, Number::kMaxRep, eMax + 1), mode);
            checkOfNumber(makeNumberPair(false, Number::minMantissa(), -200), mode);

            // Arithmetic at the max - same-sign max push the exponent past
            // kMaxOffset → overflow.
            checkAdd(posMax, posMax, mode);
            checkAdd(negMax, negMax, mode);
            // Exact cancellation at the extreme → zero, no overflow.
            checkAdd(posMax, negMax, mode);

            // Extreme ± smallest: the tiny operand is below precision and dropped.
            checkAdd(posMax, posMin, mode);
            checkAdd(negMax, negMin, mode);

            // Smallest nonzero accumulation / cancellation.
            checkAdd(posMin, posMin, mode);
            checkAdd(posMin, negMin, mode);

            // Maximal exponent spread: kMinValue@kMinOffset + kMaxValue@kMaxOffset
            // — the tiny operand is below precision and is dropped.
            checkAdd(makeIOUAmountPair(kMin, eMin), makeIOUAmountPair(kMax, eMax), mode);
        }
        // Note: IOUAmount has no Unchecked ctor, so operation inputs must be
        // canonical (above). Raw int64 mantissa-field extremes are exercised in
        // test_known_construction / test_fuzz_construction, where both sides run
        // the same normalize(raw mantissa, exp).
    }

    // ---- Cusp sweeps ----

    void
    testRangeSweep()
    {
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        for (auto const mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            sweepRange(mode);
            sweepSumOverflow(mode);
        }
    }

    // Normalizing (mantissa, exponent): past 16 digits at exponent 80 overflows, below 16 digits
    // at exponent -96 is zero.
    void
    sweepRange(Number::RoundingMode mode)
    {
        beginCase(("LeanIOUAmount.range " + modeName(mode) + "-Sweep").c_str());
        runAroundCusp(kIouRangeCases, [&](Scaled const& c) {
            checkOfMantissaExp(c.mantissa, c.exponent, mode);
            return cppVerdict(
                [&] { return IOUAmount{c.mantissa, static_cast<int>(c.exponent)}.signum() == 0; });
        });
    }

    // Add at exponent 80: a mantissa sum up to 16 digits fits, one more overflows.
    void
    sweepSumOverflow(Number::RoundingMode mode)
    {
        beginCase(("LeanIOUAmount.add overflow " + modeName(mode) + "-Sweep").c_str());
        runAroundCusp(kIouSumOverflowCases, [&](MantissaPair const& c) {
            auto const a = makeIOUAmountPair(c.a, c.exponent);
            auto const b = makeIOUAmountPair(c.b, c.exponent);
            checkAdd(a, b, mode);
            return cppVerdict([&] { return (a.cppIou + b.cppIou).signum() == 0; });
        });
    }

private:
    void
    runTests() override
    {
        // IOUAmount normalizes through Number on both sides (C++ retired the switchover in #5962).
        test_fuzz_construction();
        test_fuzz_conversion();
        test_fuzz_arithmetic();
        test_known_construction();
        test_known_arithmetic();
        test_extreme_values();
        testRangeSweep();
    }
};

BEAST_DEFINE_TESTSUITE(LeanIOUAmount, formal_verification, xrpl);

}  // namespace xrpl::test
