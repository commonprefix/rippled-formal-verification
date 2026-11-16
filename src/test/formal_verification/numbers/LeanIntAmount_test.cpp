#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/Int64FFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberHelpers.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/MPTAmount.h>
#include <xrpl/protocol/Protocol.h>

#include <cstddef>
#include <cstdint>
#include <exception>
#include <initializer_list>
#include <limits>
#include <optional>
#include <sstream>
#include <string>

extern "C" {
lean_object*
lean_int_amount_of_number(lean_object* number, uint8_t mode);
lean_object*
lean_int_amount_to_number(int64_t v, uint8_t mode);
}

namespace xrpl::test {

using namespace formal_verification;

namespace {

// A Number mantissa * 10^exponent, as ToNearest stores it.
struct OfNumberCase
{
    std::int64_t mantissa;
    int exponent;
    TER expected;
};

// An int64, and the Number C++ converts it to.
struct ToNumberCase
{
    std::int64_t value;
    ScaledValue expected;
    std::optional<Number::RoundingMode> mode{};
};

std::string
text(OfNumberCase const& c, Number::RoundingMode mode)
{
    return std::to_string(c.mantissa) + "e" + std::to_string(c.exponent) + ", " + modeName(mode);
}

std::string
text(ToNumberCase const& c, Number::RoundingMode mode)
{
    return std::to_string(c.value) + ", " + modeName(mode);
}

}  // namespace

class LeanIntAmount_test : public LeanSuite
{
    static std::string
    fmtVal(int64_t v)
    {
        std::stringstream ss;
        ss << v;
        return ss.str();
    }

    TER
    checkOfNumber(NumberPair const& p, Number::RoundingMode mode)
    {
        auto lean = readExcept<Int64FFI>(lean_int_amount_of_number(
            lean_number_build(
                p.leanNum.negative, p.leanNum.mantissa, static_cast<int64_t>(p.leanNum.exponent)),
            toLeanMode(mode)));
        bool cppThrew = false;
        int64_t cpp = 0;
        try
        {
            cpp = MPTAmount{p.cppNum}.value();
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        auto label = [&] {
            std::stringstream ss;
            ss << "ofNumber(" << (p.leanNum.negative ? "-" : "+") << p.leanNum.mantissa << "e"
               << p.cppNum.exponent() << ")";
            return ss.str();
        };
        TER const verdict = cppVerdict(cppThrew, !cppThrew && cpp == 0);
        if (lean.value.has_value() == cppThrew)
        {
            fail(
                label() + ": error mismatch lean.ok=" + (lean.value.has_value() ? "1" : "0") +
                " cppThrew=" + (cppThrew ? "1" : "0"));
            return verdict;
        }
        if (!lean.value.has_value())
        {
            pass();
            return verdict;
        }
        if (lean.value->read() != cpp)
        {
            std::stringstream ss;
            ss << label() << ": value mismatch lean=" << lean.value->read() << " cpp=" << cpp;
            fail(ss.str());
            return verdict;
        }
        pass();
        return verdict;
    }

    // toNumber: C++ side is the implicit `operator Number()` ctor
    TER
    checkToNumber(MPTAmountPair const& p, Number::RoundingMode mode)
    {
        auto lean = NumberFFI::fromExcept(lean_int_amount_to_number(p.leanMpt, toLeanMode(mode)));
        Number cpp = static_cast<Number>(p.cppMpt);
        TER const verdict = cppVerdict(false, cpp.signum() == 0);
        if (!lean.ok)
        {
            fail("toNumber(" + fmtVal(p.leanMpt) + "): Lean returned error");
            return verdict;
        }
        if (!fieldsEqual(lean, cpp))
        {
            std::stringstream ss;
            ss << "toNumber(" << p.leanMpt << "): mismatch lean=" << format(lean)
               << " cpp=" << format(cpp);
            fail(ss.str());
            return verdict;
        }
        pass();
        return verdict;
    }

public:
    void
    test_fuzz_of_number()
    {
        beginCase("LeanIntAmount.fuzz_of_number", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(50'000, [&] { return checkOfNumber(randomNumberPair(-100, 100), mode); });
        }
    }

    void
    test_fuzz_to_number()
    {
        beginCase("LeanIntAmount.fuzz_to_number", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(50'000, [&] { return checkToNumber(randomMPTAmountPair(), mode); });
        }
    }

    void
    test_known_values()
    {
        beginCase("LeanIntAmount.known_values");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        SaveNumberRoundMode save{Number::setround(Number::RoundingMode::ToNearest)};

        constexpr int64_t int64Max = std::numeric_limits<int64_t>::max();
        constexpr int64_t e18 = 1'000'000'000'000'000'000LL;
        static_assert(
            static_cast<int64_t>(kMaxMpTokenAmount) == int64Max,
            "kMaxMpTokenAmount must equal INT64_MAX");

        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode m{Number::setround(mode)};
            checkToNumber(makeMPTAmountPair(0), mode);
            checkToNumber(makeMPTAmountPair(1), mode);
            checkToNumber(makeMPTAmountPair(-1), mode);
            checkToNumber(makeMPTAmountPair(1'000'000'000LL), mode);
            checkToNumber(makeMPTAmountPair(-1'000'000'000LL), mode);

            checkOfNumber(makeNumberPair(false, 0, 0), mode);
            checkOfNumber(makeNumberPair(false, e18, 0), mode);
            checkOfNumber(makeNumberPair(true, e18, 0), mode);
            // Fractional input: each mode rounds differently.
            checkOfNumber(makeNumberPair(false, 1'234'567'890'123'456'789ULL, -2), mode);
            checkOfNumber(makeNumberPair(true, 1'234'567'890'123'456'789ULL, -2), mode);
        }
    }

    void
    test_extreme_values()
    {
        beginCase("LeanIntAmount.extreme_values");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        SaveNumberRoundMode save{Number::setround(Number::RoundingMode::ToNearest)};

        constexpr int64_t int64Min = std::numeric_limits<int64_t>::min();
        constexpr int64_t kMax = static_cast<int64_t>(kMaxMpTokenAmount);

        // toNumber at the int64 boundaries. INT64_MIN is included
        for (int64_t v : {int64Min, int64Min + 1, -kMax, int64_t{-1}, int64_t{0}, int64_t{1}, kMax})
            checkToNumber(makeMPTAmountPair(v), Number::RoundingMode::ToNearest);

        // ofNumber at boundary mantissas + overflow via large exponent.
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode m{Number::setround(mode)};
            checkOfNumber(makeNumberPair(false, Number::minMantissa(), 0), mode);
            checkOfNumber(makeNumberPair(false, Number::kMaxRep, 0), mode);
            checkOfNumber(makeNumberPair(true, Number::kMaxRep, 0), mode);
            checkOfNumber(makeNumberPair(false, Number::kMaxRep, -18), mode);
            checkOfNumber(makeNumberPair(true, Number::kMaxRep, -18), mode);
            checkOfNumber(makeNumberPair(false, Number::kMaxRep, 5), mode);
            checkOfNumber(makeNumberPair(true, Number::kMaxRep, 5), mode);
        }
    }

    // One test case per list; each row compares Lean with C++, then the C++ result with the row.
    void
    testBoundaries()
    {
        auto const ofNumber = [&](std::size_t i, OfNumberCase const& c, Number::RoundingMode mode) {
            expectResult(
                i,
                text(c, mode),
                checkOfNumber(storedNumber(c.mantissa, c.exponent), mode),
                c.expected);
        };
        auto const toNumber = [&](std::size_t i, ToNumberCase const& c, Number::RoundingMode mode) {
            auto const p = makeMPTAmountPair(c.value);
            checkToNumber(p, mode);
            Number const r = static_cast<Number>(p.cppMpt);
            expectResult(i, text(c, mode), ScaledValue{r.mantissa(), r.exponent()}, c.expected);
        };

        runRows(*this, "LeanIntAmount.ofNumber int64 max", kOfNumber, ofNumber);
        runRows(*this, "LeanIntAmount.toNumber int64 min", kToNumber, toNumber);
    }

private:
    // Each list runs its rows under every rounding mode on the large mantissa scale; a row that
    // names a mode runs under that mode only, as its result depends on the mode. A group comment
    // names the row on the cusp; its rows move the mantissa and exponent around it.
    // - kOfNumber: Number to int64. Up to int64 max converts; one Number above throws
    //   (tecPATH_DRY); zero is tecPRECISION_LOSS. The input is m * 10^e as ToNearest stores it, so
    //   the rows at -2^63 convert -kMaxRep (9'223'372'036'854'775'807).
    // - kToNumber: int64 to Number around INT64_MIN. 2^63 lies between kMaxRep and kMaxRepUp
    //   (9'223'372'036'854'775'810): Downward gives -kMaxRepUp, the other modes -kMaxRep. The rows
    //   hold the Number C++ returns.
    // clang-format off
    static constexpr OfNumberCase kOfNumber[] = {
        // 9'223'372'036'854'775'807e0
        {.mantissa = 9'223'372'036'854'775'805, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'805, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'805, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'805, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'036'854'775'805, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'036'854'775'806, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'806, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'806, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'806, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'036'854'775'806, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'036'854'775'807, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'807, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'807, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036'854'775'807, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'036'854'775'807, .exponent = 2, .expected = tecPATH_DRY},
        // 922'337'203'685'477'580e1
        {.mantissa = 922'337'203'685'477'578, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'578, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'578, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'578, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'578, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'579, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'579, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'579, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'579, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'579, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'580, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'580, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'580, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'580, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'580, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'581, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'581, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'581, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'581, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'581, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'582, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'582, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 922'337'203'685'477'582, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'582, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 922'337'203'685'477'582, .exponent = 3, .expected = tecPATH_DRY},
        // 9'223'372'036e9
        {.mantissa = 9'223'372'034, .exponent = 7, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'034, .exponent = 8, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'034, .exponent = 9, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'034, .exponent = 10, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'034, .exponent = 11, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'035, .exponent = 7, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'035, .exponent = 8, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'035, .exponent = 9, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'035, .exponent = 10, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'035, .exponent = 11, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'036, .exponent = 7, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036, .exponent = 8, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036, .exponent = 9, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'036, .exponent = 10, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'036, .exponent = 11, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'037, .exponent = 7, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'037, .exponent = 8, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'037, .exponent = 9, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'037, .exponent = 10, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'037, .exponent = 11, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'038, .exponent = 7, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'038, .exponent = 8, .expected = tesSUCCESS},
        {.mantissa = 9'223'372'038, .exponent = 9, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'038, .exponent = 10, .expected = tecPATH_DRY},
        {.mantissa = 9'223'372'038, .exponent = 11, .expected = tecPATH_DRY},
        // 9e18
        {.mantissa = 7, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 7, .exponent = 17, .expected = tesSUCCESS},
        {.mantissa = 7, .exponent = 18, .expected = tesSUCCESS},
        {.mantissa = 7, .exponent = 19, .expected = tecPATH_DRY},
        {.mantissa = 7, .exponent = 20, .expected = tecPATH_DRY},
        {.mantissa = 8, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 8, .exponent = 17, .expected = tesSUCCESS},
        {.mantissa = 8, .exponent = 18, .expected = tesSUCCESS},
        {.mantissa = 8, .exponent = 19, .expected = tecPATH_DRY},
        {.mantissa = 8, .exponent = 20, .expected = tecPATH_DRY},
        {.mantissa = 9, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 9, .exponent = 17, .expected = tesSUCCESS},
        {.mantissa = 9, .exponent = 18, .expected = tesSUCCESS},
        {.mantissa = 9, .exponent = 19, .expected = tecPATH_DRY},
        {.mantissa = 9, .exponent = 20, .expected = tecPATH_DRY},
        {.mantissa = 10, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 10, .exponent = 17, .expected = tesSUCCESS},
        {.mantissa = 10, .exponent = 18, .expected = tecPATH_DRY},
        {.mantissa = 10, .exponent = 19, .expected = tecPATH_DRY},
        {.mantissa = 10, .exponent = 20, .expected = tecPATH_DRY},
        {.mantissa = 11, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 11, .exponent = 17, .expected = tesSUCCESS},
        {.mantissa = 11, .exponent = 18, .expected = tecPATH_DRY},
        {.mantissa = 11, .exponent = 19, .expected = tecPATH_DRY},
        {.mantissa = 11, .exponent = 20, .expected = tecPATH_DRY},
        // -9'223'372'036'854'775'807e0
        {.mantissa = -9'223'372'036'854'775'807 - 1, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'807 - 1, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'807 - 1, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'807 - 1, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -9'223'372'036'854'775'807 - 1, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -9'223'372'036'854'775'807, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'807, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'807, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'807, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -9'223'372'036'854'775'807, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -9'223'372'036'854'775'806, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'806, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'806, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'806, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -9'223'372'036'854'775'806, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -9'223'372'036'854'775'805, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'805, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'805, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -9'223'372'036'854'775'805, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -9'223'372'036'854'775'805, .exponent = 2, .expected = tecPATH_DRY},
        // -922'337'203'685'477'580e1
        {.mantissa = -922'337'203'685'477'582, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'582, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'582, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'582, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'582, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'581, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'581, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'581, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'581, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'581, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'580, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'580, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'580, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'580, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'580, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'579, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'579, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'579, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'579, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'579, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'578, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'578, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'578, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = -922'337'203'685'477'578, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -922'337'203'685'477'578, .exponent = 3, .expected = tecPATH_DRY},
    };
    static constexpr ToNumberCase kToNumber[] = {
        // -9'223'372'036'854'775'807
        {.value = -9'223'372'036'854'775'807 - 1, .expected = {.mantissa = -9'223'372'036'854'775'807, .exponent = 0}, .mode = Number::RoundingMode::ToNearest},
        {.value = -9'223'372'036'854'775'807 - 1, .expected = {.mantissa = -9'223'372'036'854'775'807, .exponent = 0}, .mode = Number::RoundingMode::TowardsZero},
        {.value = -9'223'372'036'854'775'807 - 1, .expected = {.mantissa = -922'337'203'685'477'581, .exponent = 1}, .mode = Number::RoundingMode::Downward},
        {.value = -9'223'372'036'854'775'807 - 1, .expected = {.mantissa = -9'223'372'036'854'775'807, .exponent = 0}, .mode = Number::RoundingMode::Upward},
        {.value = -9'223'372'036'854'775'807, .expected = {.mantissa = -9'223'372'036'854'775'807, .exponent = 0}},
        {.value = -9'223'372'036'854'775'806, .expected = {.mantissa = -9'223'372'036'854'775'806, .exponent = 0}},
        {.value = -9'223'372'036'854'775'805, .expected = {.mantissa = -9'223'372'036'854'775'805, .exponent = 0}},
    };
    // clang-format on

    void
    runTests() override
    {
        test_fuzz_of_number();
        test_fuzz_to_number();
        test_known_values();
        test_extreme_values();
        testBoundaries();
    }
};

BEAST_DEFINE_TESTSUITE(LeanIntAmount, formal_verification, xrpl);

}  // namespace xrpl::test
