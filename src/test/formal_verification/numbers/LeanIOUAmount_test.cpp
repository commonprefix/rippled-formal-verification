#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/protocol/IOUAmountFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberHelpers.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/IOUAmount.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <limits>
#include <optional>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>

// Lean IOUAmount ops (exported by xrpl-lean4/XRPL/IOUAmount/FFI.lean).
extern "C" {
lean_object*
lean_iou_amount_build(int64_t mantissa, int64_t exponent);
lean_object*
lean_iou_of_mantissa_exp(int64_t, int64_t, uint8_t);
lean_object*
lean_iou_of_number(lean_object*, uint8_t);
lean_object*
lean_iou_from_number(lean_object*, uint8_t);
lean_object*
lean_iou_to_number(lean_object*, uint8_t);
lean_object*
lean_iou_add(lean_object*, lean_object*, uint8_t);
}

namespace xrpl::test {

using namespace formal_verification;

namespace {

// An IOU mantissa * 10^exponent, or the Number m * 10^e as ToNearest stores it.
struct IouCase
{
    std::int64_t mantissa;
    int exponent;
    TER expected;
    std::optional<Number::RoundingMode> mode{};
};

// The Number m * 10^e as ToNearest stores it, and the IOU mantissa and exponent C++ rounds it to.
struct IouValueCase
{
    std::int64_t mantissa;
    int exponent;
    ScaledValue expected;
    std::optional<Number::RoundingMode> mode{};
};

// Two IOU mantissas at one exponent.
struct IouPairCase
{
    std::int64_t a;
    std::int64_t b;
    int exponent;
    TER expected;
};

std::string
text(std::int64_t mantissa, int exponent, Number::RoundingMode mode)
{
    return std::to_string(mantissa) + "e" + std::to_string(exponent) + ", " + modeName(mode);
}

std::string
text(IouPairCase const& c, char op, Number::RoundingMode mode)
{
    return std::to_string(c.a) + ' ' + op + ' ' + std::to_string(c.b) + " at exponent " +
        std::to_string(c.exponent) + ", " + modeName(mode);
}

}  // namespace

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

    // Compare a Lean IOUAmount result to a C++ outcome (which may throw); returns the C++ verdict.
    TER
    checkIOUResult(
        std::string const& label,
        LeanIOUResult const& lean,
        IOUAmount const& cpp,
        bool cppThrew)
    {
        TER const verdict = cppVerdict(cppThrew, !cppThrew && cpp.signum() == 0);
        if (lean.ok == cppThrew)
        {
            std::stringstream ss;
            ss << label << ": error mismatch (lean." << (lean.ok ? "ok" : "error") << ", cpp."
               << (cppThrew ? "threw" : "ok") << ")";
            fail(ss.str());
            return verdict;
        }
        if (!lean.ok)
        {
            pass();
            return verdict;
        }
        if (lean.mantissa != cpp.mantissa() || lean.exponent != cpp.exponent())
        {
            std::stringstream ss;
            ss << label << ": result mismatch lean=" << fmtIOU(lean) << " cpp=" << fmtIOU(cpp);
            fail(ss.str());
            return verdict;
        }
        pass();
        return verdict;
    }

    // ofMantissaExp ↔ IOUAmount{m, e}.
    TER
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
    TER
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

    // fromNumber ↔ Number::normalizeToRange into the IOU mantissa range, which C++ IOUAmount uses
    // before its exponent check.
    TER
    checkFromNumber(NumberPair const& p, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        auto lean = IOUAmountFFI::fromExcept(lean_iou_from_number(
            lean_number_build(
                p.leanNum.negative, p.leanNum.mantissa, static_cast<int64_t>(p.leanNum.exponent)),
            toLeanMode(mode)));
        std::pair<std::int64_t, int> cpp{0, 0};
        bool cppThrew = false;
        try
        {
            cpp = p.cppNum.normalizeToRange<kIouMinMantissa, kIouMaxMantissa>();
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        std::stringstream label;
        label << "fromNumber(" << (p.leanNum.negative ? "-" : "+") << p.leanNum.mantissa << "e"
              << p.cppNum.exponent() << ")";
        TER const verdict = cppVerdict(cppThrew, !cppThrew && cpp.first == 0);
        if (lean.ok == cppThrew)
        {
            fail(label.str() + ": error mismatch");
            return verdict;
        }
        if (lean.ok && (lean.mantissa != cpp.first || lean.exponent != cpp.second))
        {
            fail(
                label.str() + ": result mismatch lean=" + fmtIOU(lean) +
                " cpp=" + fmtIOU(cpp.first, cpp.second));
            return verdict;
        }
        pass();
        return verdict;
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

    TER
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

        for (auto mode : kRoundingModes)
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
        for (auto mode : kRoundingModes)
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
        for (auto mode : kRoundingModes)
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

        for (auto mode : kRoundingModes)
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
        for (auto mode : kRoundingModes)
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

        for (auto mode : kRoundingModes)
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

    // One test case per list; each row compares Lean with C++, then the C++ result with the row.
    void
    testBoundaries()
    {
        auto const range = [&](std::size_t i, IouCase const& c, Number::RoundingMode mode) {
            expectResult(
                i,
                text(c.mantissa, c.exponent, mode),
                checkOfMantissaExp(c.mantissa, c.exponent, mode),
                c.expected);
        };
        auto const ofNumber = [&](std::size_t i, IouCase const& c, Number::RoundingMode mode) {
            expectResult(
                i,
                text(c.mantissa, c.exponent, mode),
                checkOfNumber(storedNumber(c.mantissa, c.exponent), mode),
                c.expected);
        };
        auto const fromNumber =
            [&](std::size_t i, IouValueCase const& c, Number::RoundingMode mode) {
                auto const n = storedNumber(c.mantissa, c.exponent);
                checkFromNumber(n, mode);
                auto const [m, e] = n.cppNum.normalizeToRange<kIouMinMantissa, kIouMaxMantissa>();
                expectResult(i, text(c.mantissa, c.exponent, mode), ScaledValue{m, e}, c.expected);
            };
        auto const sum = [&](std::size_t i, IouPairCase const& c, Number::RoundingMode mode) {
            TER const verdict = checkAdd(
                makeIOUAmountPair(c.a, c.exponent), makeIOUAmountPair(c.b, c.exponent), mode);
            expectResult(i, text(c, '+', mode), verdict, c.expected);
        };
        auto const difference =
            [&](std::size_t i, IouPairCase const& c, Number::RoundingMode mode) {
                TER const verdict = checkAdd(
                    makeIOUAmountPair(c.a, c.exponent), makeIOUAmountPair(-c.b, c.exponent), mode);
                expectResult(i, text(c, '-', mode), verdict, c.expected);
            };

        runRows(*this, "LeanIOUAmount.range", kRange, range);
        runRows(*this, "LeanIOUAmount.range, by mode", kRangeByMode, range);
        runRows(*this, "LeanIOUAmount.ofNumber", kOfNumber, ofNumber);
        runRows(*this, "LeanIOUAmount.fromNumber", kFromNumber, fromNumber);
        runRows(*this, "LeanIOUAmount.fromNumber, by mode", kFromNumberByMode, fromNumber);
        // Every sum is exact, so one mode covers them.
        runRows(*this, "LeanIOUAmount.add overflow", kSumOverflow, sum, kToNearestOnly);
        runRows(
            *this, "LeanIOUAmount.add underflow", kDifferenceUnderflow, difference, kToNearestOnly);
    }

private:
    // Each list runs its rows under every rounding mode on the large mantissa scale (the sums under
    // ToNearest only); a row that names a mode runs under that mode only, as its result depends on
    // the mode. A group comment names the row on the cusp; its rows move two values around it.
    // An IOU keeps 16 digits (10^15 to 10^16 - 1) at exponents -96 to 80.
    // - kRange: normalizing (mantissa, exponent). Past 16 digits at exponent 80 throws
    //   (tecPATH_DRY), below them at -96 is zero (tecPRECISION_LOSS); 17 digits at 79 round into
    //   exponent 80 or past it as the mode rounds them (kRangeByMode).
    // - kOfNumber: Number m * 10^e (19 digits, as ToNearest stores it) to IOU. 10^16 - 1/2 at
    //   exponent 80 rounds into an overflow (tecPATH_DRY) under ToNearest, away from zero under the
    //   directed modes; the smallest IOU at -96, one ULP less rounds to zero (tecPRECISION_LOSS) or
    //   back up into range.
    // - kFromNumber: the same Numbers rounded to 16 digits before the exponent check; nothing
    // throws.
    //   The rows hold the mantissa and exponent C++ returns; most depend on the mode
    //   (kFromNumberByMode, cusp rows and their one-step moves only).
    // - kSumOverflow: add at exponent 80. A sum up to 10^16 - 1 fits, one more throws
    //   (tecPATH_DRY).
    // - kDifferenceUnderflow: a + (-b) at exponent -96. a - b down to 10^15 is a value, one less is
    //   zero (tecPRECISION_LOSS).
    // clang-format off
    static constexpr IouCase kRange[] = {
        // 9'999'999'999'999'999e80
        {.mantissa = 9'999'999'999'999'997, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'997, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'997, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'997, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'998, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'998, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'998, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'998, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'999, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'999, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'999, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'999, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'000, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'000, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'000, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'000, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'001, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'001, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'001, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'001, .exponent = 82, .expected = tecPATH_DRY},
        // 1'000'000'000'000'000e-96
        {.mantissa = 999'999'999'999'998, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'998, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'998, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'998, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'998, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'999, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'999, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'999, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'001, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'001, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'001, .exponent = -96, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'001, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'001, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'002, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'002, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'002, .exponent = -96, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'002, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'002, .exponent = -94, .expected = tesSUCCESS},
        // 99'999'999'999'999'994e79
        {.mantissa = 99'999'999'999'999'992, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'992, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'992, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'992, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'993, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'993, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'993, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'993, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'994, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'994, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'994, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'994, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'995, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'995, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'995, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'995, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'996, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'996, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'996, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'996, .exponent = 81, .expected = tecPATH_DRY},
        // -9'999'999'999'999'999e80
        {.mantissa = -10'000'000'000'000'001, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -10'000'000'000'000'001, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = -10'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -10'000'000'000'000'001, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -10'000'000'000'000'001, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = -10'000'000'000'000'000, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -10'000'000'000'000'000, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = -10'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -10'000'000'000'000'000, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -10'000'000'000'000'000, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = -9'999'999'999'999'999, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'999, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'999, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -9'999'999'999'999'999, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = -9'999'999'999'999'998, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'998, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'998, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -9'999'999'999'999'998, .exponent = 82, .expected = tecPATH_DRY},
        {.mantissa = -9'999'999'999'999'997, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'997, .exponent = 79, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.mantissa = -9'999'999'999'999'997, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -9'999'999'999'999'997, .exponent = 82, .expected = tecPATH_DRY},
        // -1'000'000'000'000'000e-96
        {.mantissa = -1'000'000'000'000'002, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'002, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'002, .exponent = -96, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'002, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'002, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'001, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'001, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'001, .exponent = -96, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'001, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'001, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999, .exponent = -94, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'998, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'998, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'998, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'998, .exponent = -95, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'998, .exponent = -94, .expected = tesSUCCESS},
        // -99'999'999'999'999'994e79
        {.mantissa = -99'999'999'999'999'996, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'996, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'996, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'996, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'995, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'995, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'995, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'995, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'994, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'994, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'994, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'994, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'993, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'993, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'993, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'993, .exponent = 81, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'992, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'992, .exponent = 78, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'992, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'992, .exponent = 81, .expected = tecPATH_DRY},
    };
    static constexpr IouCase kRangeByMode[] = {
        // 99'999'999'999'999'994e79
        {.mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        // -99'999'999'999'999'994e79
        {.mantissa = -99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -99'999'999'999'999'994, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -99'999'999'999'999'993, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -99'999'999'999'999'992, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
    };
    static constexpr IouCase kOfNumber[] = {
        // 999'999'999'999'999'950e78
        {.mantissa = 999'999'999'999'999'948, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'948, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'948, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'948, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'948, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'949, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'949, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'949, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'949, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'950, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'950, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'950, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'951, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'951, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'951, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'952, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'952, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'952, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'952, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'952, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'952, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'952, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = 999'999'999'999'999'952, .exponent = 80, .expected = tecPATH_DRY},
        // -999'999'999'999'999'950e78
        {.mantissa = -999'999'999'999'999'952, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'952, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'952, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'952, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'952, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'952, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'952, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'952, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'951, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'951, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'951, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'950, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'950, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'950, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'949, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'949, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'949, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'948, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'948, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'948, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'948, .exponent = 80, .expected = tecPATH_DRY},
        // 1'000'000'000'000'000'000e-99
        {.mantissa = 999'999'999'999'999'998, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'999'998, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'999'998, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'998, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'998, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'998, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'998, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'998, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'999, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'999'999, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'999, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = 999'999'999'999'999'999, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -99, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -99, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'002, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000'002, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = 1'000'000'000'000'000'002, .exponent = -99, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'002, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = 1'000'000'000'000'000'002, .exponent = -97, .expected = tesSUCCESS},
        // -1'000'000'000'000'000'000e-99
        {.mantissa = -1'000'000'000'000'000'002, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000'002, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000'002, .exponent = -99, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'002, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'002, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -99, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -99, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'999, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999'999, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'999, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'998, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -97, .expected = tesSUCCESS},
    };
    static constexpr IouValueCase kFromNumber[] = {
        // 1'000'000'000'000'000'000e-99
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -101, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -98}},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -100, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -97}},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -99, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -96}},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -98, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -95}},
        {.mantissa = 1'000'000'000'000'000'000, .exponent = -97, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -94}},
        // -1'000'000'000'000'000'000e-99
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -101, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -98}},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -100, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -97}},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -99, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -96}},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -98, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -95}},
        {.mantissa = -1'000'000'000'000'000'000, .exponent = -97, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -94}},
    };
    static constexpr IouValueCase kFromNumberByMode[] = {
        // 999'999'999'999'999'950e78
        {.mantissa = 999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::Upward},
        // -999'999'999'999'999'950e78
        {.mantissa = -999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 77, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 79, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 77, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 79, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 80}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 77, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 79}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 81}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 80}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = 82}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 79, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = 81}, .mode = Number::RoundingMode::Upward},
        // 1'000'000'000'000'000'000e-99
        {.mantissa = 999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -98}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -98}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -97}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -97}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -96}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -96}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = 1'000'000'000'000'001, .exponent = -97}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = 1'000'000'000'000'001, .exponent = -96}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = 1'000'000'000'000'001, .exponent = -95}, .mode = Number::RoundingMode::Upward},
        // -1'000'000'000'000'000'000e-99
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = -1'000'000'000'000'001, .exponent = -97}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -100, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = -1'000'000'000'000'001, .exponent = -96}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -99, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = -1'000'000'000'000'001, .exponent = -95}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'001, .exponent = -98, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = -98}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -97}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -100, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = -98}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = -97}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -96}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = -97}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = -96}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -95}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -98, .expected = {.mantissa = -9'999'999'999'999'999, .exponent = -96}, .mode = Number::RoundingMode::Upward},
    };
    static constexpr IouPairCase kSumOverflow[] = {
        // 1'000'000'000'000'000 + 8'999'999'999'999'999 at exponent 80
        {.a = 1'000'000'000'000'000, .b = 8'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000, .b = 8'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000, .b = 8'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000, .b = 9'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000, .b = 9'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'001, .b = 8'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'001, .b = 8'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'001, .b = 8'999'999'999'999'999, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'001, .b = 9'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'001, .b = 9'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'002, .b = 8'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'002, .b = 8'999'999'999'999'998, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'002, .b = 8'999'999'999'999'999, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'002, .b = 9'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'002, .b = 9'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        // 8'999'999'999'999'999 + 1'000'000'000'000'000 at exponent 80
        {.a = 8'999'999'999'999'997, .b = 1'000'000'000'000'000, .exponent = 80, .expected = tesSUCCESS},
        {.a = 8'999'999'999'999'997, .b = 1'000'000'000'000'001, .exponent = 80, .expected = tesSUCCESS},
        {.a = 8'999'999'999'999'997, .b = 1'000'000'000'000'002, .exponent = 80, .expected = tesSUCCESS},
        {.a = 8'999'999'999'999'998, .b = 1'000'000'000'000'000, .exponent = 80, .expected = tesSUCCESS},
        {.a = 8'999'999'999'999'998, .b = 1'000'000'000'000'001, .exponent = 80, .expected = tesSUCCESS},
        {.a = 8'999'999'999'999'998, .b = 1'000'000'000'000'002, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 8'999'999'999'999'999, .b = 1'000'000'000'000'000, .exponent = 80, .expected = tesSUCCESS},
        {.a = 8'999'999'999'999'999, .b = 1'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 8'999'999'999'999'999, .b = 1'000'000'000'000'002, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 9'000'000'000'000'000, .b = 1'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 9'000'000'000'000'000, .b = 1'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 9'000'000'000'000'000, .b = 1'000'000'000'000'002, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 9'000'000'000'000'001, .b = 1'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 9'000'000'000'000'001, .b = 1'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 9'000'000'000'000'001, .b = 1'000'000'000'000'002, .exponent = 80, .expected = tecPATH_DRY},
        // 5'000'000'000'000'000 + 4'999'999'999'999'999 at exponent 80
        {.a = 4'999'999'999'999'998, .b = 4'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'998, .b = 4'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'998, .b = 4'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'998, .b = 5'000'000'000'000'000, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'998, .b = 5'000'000'000'000'001, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999, .b = 4'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999, .b = 4'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999, .b = 4'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999, .b = 5'000'000'000'000'000, .exponent = 80, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999, .b = 5'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'000, .b = 4'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000, .b = 4'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000, .b = 4'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000, .b = 5'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'000, .b = 5'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'001, .b = 4'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'001, .b = 4'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'001, .b = 4'999'999'999'999'999, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'001, .b = 5'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'001, .b = 5'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'002, .b = 4'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'002, .b = 4'999'999'999'999'998, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'002, .b = 4'999'999'999'999'999, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'002, .b = 5'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.a = 5'000'000'000'000'002, .b = 5'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
    };
    static constexpr IouPairCase kDifferenceUnderflow[] = {
        // 1'999'999'999'999'999 - 1'000'000'000'000'000 at exponent -96
        {.a = 1'999'999'999'999'997, .b = 1'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'997, .b = 1'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'997, .b = 1'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'998, .b = 1'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'998, .b = 1'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'998, .b = 1'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999, .b = 1'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999, .b = 1'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999, .b = 1'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'000, .b = 1'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000, .b = 1'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'000, .b = 1'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'001, .b = 1'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'001, .b = 1'000'000'000'000'001, .exponent = -96, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'001, .b = 1'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        // 9'999'999'999'999'999 - 9'000'000'000'000'000 at exponent -96
        {.a = 9'999'999'999'999'997, .b = 8'999'999'999'999'998, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'997, .b = 8'999'999'999'999'999, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'997, .b = 9'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'997, .b = 9'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'997, .b = 9'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'998, .b = 8'999'999'999'999'998, .exponent = -96, .expected = tesSUCCESS},
        {.a = 9'999'999'999'999'998, .b = 8'999'999'999'999'999, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'998, .b = 9'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'998, .b = 9'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'998, .b = 9'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'999, .b = 8'999'999'999'999'998, .exponent = -96, .expected = tesSUCCESS},
        {.a = 9'999'999'999'999'999, .b = 8'999'999'999'999'999, .exponent = -96, .expected = tesSUCCESS},
        {.a = 9'999'999'999'999'999, .b = 9'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'999, .b = 9'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 9'999'999'999'999'999, .b = 9'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        // 5'000'000'000'000'000 - 4'000'000'000'000'001 at exponent -96
        {.a = 4'999'999'999'999'998, .b = 3'999'999'999'999'999, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'998, .b = 4'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'998, .b = 4'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'998, .b = 4'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'998, .b = 4'000'000'000'000'003, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999, .b = 3'999'999'999'999'999, .exponent = -96, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999, .b = 4'000'000'000'000'000, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999, .b = 4'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999, .b = 4'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999, .b = 4'000'000'000'000'003, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000, .b = 3'999'999'999'999'999, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000, .b = 4'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000, .b = 4'000'000'000'000'001, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000, .b = 4'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000, .b = 4'000'000'000'000'003, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'001, .b = 3'999'999'999'999'999, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'001, .b = 4'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'001, .b = 4'000'000'000'000'001, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'001, .b = 4'000'000'000'000'002, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'001, .b = 4'000'000'000'000'003, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'002, .b = 3'999'999'999'999'999, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'002, .b = 4'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'002, .b = 4'000'000'000'000'001, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'002, .b = 4'000'000'000'000'002, .exponent = -96, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'002, .b = 4'000'000'000'000'003, .exponent = -96, .expected = tecPRECISION_LOSS},
    };
    // clang-format on

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
        testBoundaries();
    }
};

BEAST_DEFINE_TESTSUITE(LeanIOUAmount, formal_verification, xrpl);

}  // namespace xrpl::test
