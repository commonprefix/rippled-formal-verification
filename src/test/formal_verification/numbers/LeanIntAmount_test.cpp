#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/Int64FFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberHelpers.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/MPTAmount.h>
#include <xrpl/protocol/Protocol.h>

#include <exception>
#include <initializer_list>
#include <limits>
#include <sstream>

extern "C" {
lean_object*
lean_int_amount_of_number(lean_object* number, uint8_t mode);
lean_object*
lean_int_amount_to_number(int64_t v, uint8_t mode);
}

namespace xrpl::test {

using namespace formal_verification;

class LeanIntAmount_test : public LeanSuite
{
    static std::string
    fmtVal(int64_t v)
    {
        std::stringstream ss;
        ss << v;
        return ss.str();
    }

    bool
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
        if (lean.value.has_value() == cppThrew)
        {
            fail(
                label() + ": error mismatch lean.ok=" + (lean.value.has_value() ? "1" : "0") +
                " cppThrew=" + (cppThrew ? "1" : "0"));
            return false;
        }
        if (!lean.value.has_value())
        {
            pass();
            return true;
        }
        if (lean.value->read() != cpp)
        {
            std::stringstream ss;
            ss << label() << ": value mismatch lean=" << lean.value->read() << " cpp=" << cpp;
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    // toNumber: C++ side is the implicit `operator Number()` ctor
    bool
    checkToNumber(MPTAmountPair const& p, Number::RoundingMode mode)
    {
        auto lean = NumberFFI::fromExcept(lean_int_amount_to_number(p.leanMpt, toLeanMode(mode)));
        Number cpp = static_cast<Number>(p.cppMpt);
        if (!lean.ok)
        {
            fail("toNumber(" + fmtVal(p.leanMpt) + "): Lean returned error");
            return false;
        }
        if (!fieldsEqual(lean, cpp))
        {
            std::stringstream ss;
            ss << "toNumber(" << p.leanMpt << "): mismatch lean=" << format(lean)
               << " cpp=" << format(cpp);
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

public:
    void
    test_fuzz_of_number()
    {
        beginCase("LeanIntAmount.fuzz_of_number", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
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
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
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

        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
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
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
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

private:
    void
    runTests() override
    {
        test_fuzz_of_number();
        test_fuzz_to_number();
        test_known_values();
        test_extreme_values();
    }
};

BEAST_DEFINE_TESTSUITE(LeanIntAmount, formal_verification, xrpl);

}  // namespace xrpl::test
