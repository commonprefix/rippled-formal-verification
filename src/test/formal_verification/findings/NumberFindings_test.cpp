#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/findings/NumberFindingsHelpers.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberSweepCases.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/json/json_value.h>
#include <xrpl/protocol/AccountID.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/MPTAmount.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/UintTypes.h>
#include <xrpl/protocol/jss.h>

#include <cstdint>
#include <exception>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

namespace xrpl::test::formal_verification {

using namespace number_sweep;

// The number bugs found in Milestone 1. A Number case runs the reported inputs through the Lean
// model and C++ and expects the same result. Calls that fail are commented out in runTests(), the
// rest run as regression tests.
class NumberFindings_test : public LeanSuite
{
    // FV_M1_11: MPTAmount mulRatio returns INT64_MIN for a result below INT64_MIN instead of
    // throwing std::overflow_error.
    void
    testMptMulRatioUnderflow()
    {
        testcase("FV_M1_11 MPTAmount mulRatio underflow");

        // 1. -1087822186689188 x 477618 / 56 is below INT64_MIN.
        MPTAmount const amount{-1'087'822'186'689'188LL};
        MPTAmount result{0};
        bool threw = false;
        try
        {
            result = mulRatio(amount, 477'618, 56, true);
        }
        catch (std::overflow_error const&)
        {
            threw = true;
        }

        // BUG: mulRatio returns INT64_MIN.
        BEAST_EXPECTS(threw, "mulRatio returned " + to_string(result));
    }

    // FV_M1_12: a product, sum or difference that rounds into the range between kMaxRep and
    // kMaxRepUp is the same in the model and in C++ (XRPLF/rippled#7389).
    void
    testRangeBoundaryArithmetic()
    {
        testcase("FV_M1_12 range boundary arithmetic");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        SaveNumberRoundMode const modeGuard{Number::setround(Number::RoundingMode::ToNearest)};
        auto const maxRep = Number::kMaxRep;  // 9223372036854775807 = 2^63 - 1

        // maxRep * (1 + 1e-18)
        checkBinOp(
            *this,
            makeNumberPair(false, maxRep, 0),
            '*',
            makeNumberPair(false, 1'000'000'000'000'000'001ULL, -18));
        // maxRep + 5e18 e-18
        checkBinOp(
            *this,
            makeNumberPair(false, maxRep, 0),
            '+',
            makeNumberPair(false, 5'000'000'000'000'000'000ULL, -18));
        // 9999...90 - 7777...7 (near top of range)
        checkBinOp(
            *this,
            makeNumberPair(false, 9'999'999'999'999'999'990ULL, 0),
            '-',
            makeNumberPair(false, 7'777'777'777'777'777'777ULL, 0));
    }

    // FV_M1_12: operator* under Downward at the kMaxRep cusp is the same in the model and in C++.
    // It landed 7 ULPs below the largest Number under the exact product (XRPLF/rippled#7389).
    void
    testMultiplicationRounding()
    {
        testcase("FV_M1_12 multiplication rounding");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        SaveNumberRoundMode const modeGuard{Number::setround(Number::RoundingMode::Downward)};

        // (kMaxRep - 7) * (minMantissa + 1) under Downward.
        checkBinOp(
            *this,
            makeNumberPair(false, Number::kMaxRep - 7, 0),
            '*',
            makeNumberPair(false, Number::minMantissa() + 1, 0));
    }

    // FV_M1_12: normalizing a mantissa from kMaxRep to kMaxRepUp is the same in the model and in
    // C++, for both signs and in each rounding mode.
    void
    testCuspRounding()
    {
        testcase("FV_M1_12 normalize at the kMaxRep cusp");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);

        constexpr uint64_t kMaxRep = Number::kMaxRep;      // 2^63 - 1
        constexpr uint64_t kMaxRepUp = Number::kMaxRepUp;  // next multiple of 10

        for (auto mode : kRoundingModes)
        {
            // The model and the constructor both round in the current mode.
            SaveNumberRoundMode const modeGuard{Number::setround(mode)};
            for (uint64_t const m : {kMaxRep, kMaxRep + 1, kMaxRep + 2, kMaxRepUp})
            {
                for (bool const neg : {false, true})
                    checkNormalize(*this, neg, m, 0);
            }
        }
    }

    // FV_M1_13: operator/ under Upward at the kMaxRep cusp is the same in the model and in C++.
    // It returned a value below the exact quotient.
    void
    testDivisionRounding()
    {
        testcase("FV_M1_13 division rounding");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        SaveNumberRoundMode const modeGuard{Number::setround(Number::RoundingMode::Upward)};

        // 2 / (1e18 + 7) under Upward.
        checkBinOp(
            *this,
            makeNumberPair(false, 2'000'000'000'000'000'000ULL, -18),
            '/',
            makeNumberPair(false, 1'000'000'000'000'000'007ULL, 0));
    }

    // FV_M1_14: an add or subtract of opposite signs with a large exponent gap recovers the
    // dropped digits before it rounds, as the model does (XRPLF/rippled#7369).
    void
    testLargeGapAddSub()
    {
        testcase("FV_M1_14 large gap add and subtract");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);

        // 1. Subtraction and addition under ToNearest.
        {
            SaveNumberRoundMode const modeGuard{Number::setround(Number::RoundingMode::ToNearest)};
            checkBinOp(
                *this,
                makeNumberPair(false, 1'000'000'000'000'000'001ULL, 5),
                '-',
                makeNumberPair(false, 9'999'999'999'999'999'990ULL, -10));
            checkBinOp(
                *this,
                makeNumberPair(false, 1'234'567'890'123'456'789ULL, 3),
                '+',
                makeNumberPair(true, 9'876'543'210'987'654'320ULL, -8));
        }

        // 2. 1e20 + (-(1e18 + 1)) under TowardsZero.
        {
            SaveNumberRoundMode const modeGuard{
                Number::setround(Number::RoundingMode::TowardsZero)};
            checkBinOp(
                *this,
                makeNumberPair(false, 1'000'000'000'000'000'000ULL, 2),
                '+',
                makeNumberPair(true, 1'000'000'000'000'000'001ULL, 0));
        }
    }

    // FV_M1_15: operator< orders two negative Numbers with the same exponent by value
    // (XRPLF/rippled#7406).
    void
    testNegativeComparison()
    {
        testcase("FV_M1_15 negative comparison");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);

        // 1. -3e18 and -7e18, both at exponent 0.
        auto const a = makeNumberPair(true, 3'000'000'000'000'000'000ULL, 0);
        auto const b = makeNumberPair(true, 7'000'000'000'000'000'000ULL, 0);

        // 2. Every comparison operator gives the same answer in the model and in C++.
        checkCompare(*this, a, b);
        checkCompare(*this, b, a);

        // 3. -3e18 < -7e18 is false and -7e18 < -3e18 is true on both sides.
        BEAST_EXPECT(lean_number_lt(leanNumber(a), leanNumber(b)) == 0 && !(a.cppNum < b.cppNum));
        BEAST_EXPECT(lean_number_lt(leanNumber(b), leanNumber(a)) != 0 && (b.cppNum < a.cppNum));
    }

    // FV_M1_16: the sum of two negative Numbers that overflows the mantissa rounds in the
    // direction of the rounding mode. Downward and Upward were swapped.
    void
    testAddDirectedRounding()
    {
        testcase("FV_M1_16 add directed rounding of negative Numbers");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);

        // (-6e18) + (-6.000000000000000003e18) in each rounding mode.
        auto const a = makeNumberPair(true, 6'000'000'000'000'000'000ULL, 0);
        auto const b = makeNumberPair(true, 6'000'000'000'000'000'003ULL, 0);
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode const modeGuard{Number::setround(mode)};
            checkBinOp(*this, a, '+', b);
        }
    }

    // FV_M1_17: a ToNearest sum of opposite signs with heavy cancellation rounds to the nearer
    // Number. It picked the farther one.
    void
    testAddToNearestCancellation()
    {
        testcase("FV_M1_17 add to nearest with cancellation");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        SaveNumberRoundMode const modeGuard{Number::setround(Number::RoundingMode::ToNearest)};

        // (-1074956551220905975e28) + (5175909259972499745e22)
        checkBinOp(
            *this,
            makeNumberPair(true, 1'074'956'551'220'905'975ULL, 28),
            '+',
            makeNumberPair(false, 5'175'909'259'972'499'745ULL, 22));
    }

    // Helpers of testTopExponentOverflow, down to that test.
    // A case is an operation, one of + - * /, and its two operands.
    using Case = std::tuple<char, Number, Number>;

    // Runs each case in the mode and expects the result. A negative sign mirrors the case. No
    // expected value means that the operation is expected to throw.
    void
    expectResult(
        std::span<Case const> cases,
        Number::RoundingMode mode,
        bool negative,
        std::optional<Number> const& expected)
    {
        SaveNumberRoundMode const modeGuard{Number::setround(mode)};
        for (auto const& [op, x, y] : cases)
        {
            // The mirror of x + y is -x + -y, and the mirror of x * y is -x * y.
            bool const additive = op == '+' || op == '-';
            Number const lhs = negative ? -x : x;
            Number const rhs = negative && additive ? -y : y;
            std::optional<Number> const actual = compute(lhs, op, rhs);
            std::string const label = to_string(lhs) + ' ' + op + ' ' + to_string(rhs) + ", " +
                to_string(mode) + (actual ? ", returned " + to_string(*actual) : ", threw");
            BEAST_EXPECTS(actual == expected, label);
        }
    }

    // The exact result rounds back to top, so every operation returns top with the sign.
    void
    expectTop(std::span<Case const> cases, Number::RoundingMode mode, bool negative)
    {
        Number const top{negative, Number::kMaxRepUp, Number::kMaxExponent, Number::Normalized{}};
        expectResult(cases, mode, negative, top);
    }

    // The exact result rounds to the next Number, which is rejected, so every operation throws.
    void
    expectOverflow(std::span<Case const> cases, Number::RoundingMode mode, bool negative)
    {
        expectResult(cases, mode, negative, std::nullopt);
    }

    // FV_M1_19: at the largest exponent, add, subtract and divide return a Number the constructor
    // rejects when they round up, and throw when the rounded result fits. Multiply gets both right.
    void
    testTopExponentOverflow()
    {
        testcase("FV_M1_19 overflow at the largest exponent");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        using Mode = Number::RoundingMode;
        // The sign of the exact result, the last argument of the checks below.
        bool const positive = false;
        bool const negative = true;

        // 1. The constructor accepts top and rejects the next Number, 9223372036854775820e32768.
        BEAST_EXPECT(construct(false, Number::kMaxRepUp, Number::kMaxExponent).has_value());
        BEAST_EXPECT(!construct(false, Number::kMaxRepUp + 10, Number::kMaxExponent).has_value());
        // top is the largest Number the constructor accepts, 9223372036854775810e32768. Below,
        // top + 1 stands for 9223372036854775811e32768.
        Number const top{Number::kMaxRepUp, Number::kMaxExponent, Number::Normalized{}};

        // 2. Exact result between top and top + 1. ToNearest and rounding toward zero give top.
        Case const zeroToOne[] = {
            // The exact results are top + 0.4, top + 0.4, top + 0.22 and top + 0.53.
            {'+', top, Number{4'000'000'000'000'000'000, 32749}},
            {'-', top, Number{-4'000'000'000'000'000'000, 32749}},
            {'*', Number{1'000'000'000'000'000'001, 32750}, Number{9'223'372'036'854'775'801, 0}},
            {'/', Number{8'507'059'173'023'461'588, 32768}, Number{Number::kMaxRep, -19}},
        };
        expectTop(zeroToOne, Mode::ToNearest, positive);
        expectTop(zeroToOne, Mode::ToNearest, negative);
        expectTop(zeroToOne, Mode::TowardsZero, positive);
        expectTop(zeroToOne, Mode::TowardsZero, negative);
        expectTop(zeroToOne, Mode::Downward, positive);
        expectTop(zeroToOne, Mode::Upward, negative);
        //    Rounding away from zero gives the next Number.
        // BUG: add, subtract and divide return 9223372036854775820e32768 in these two.
        expectOverflow(zeroToOne, Mode::Upward, positive);
        expectOverflow(zeroToOne, Mode::Downward, negative);

        // 3. Exact result from top + 1 to top + 5, below the midpoint to the next Number.
        Case const oneToFive[] = {
            // The exact results are top + 3, top + 3, top + 2.22 and top + 2.70.
            {'+', top, Number{3'000'000'000'000'000'000, 32750}},
            {'-', top, Number{-3'000'000'000'000'000'000, 32750}},
            {'*', Number{1'000'000'000'000'000'001, 32750}, Number{9'223'372'036'854'775'803, 0}},
            {'/', Number{8'507'059'173'023'461'590, 32768}, Number{Number::kMaxRep, -19}},
        };
        // BUG: add, subtract and divide throw "Number::normalize 1.5" in these six.
        expectTop(oneToFive, Mode::ToNearest, positive);
        expectTop(oneToFive, Mode::ToNearest, negative);
        expectTop(oneToFive, Mode::TowardsZero, positive);
        expectTop(oneToFive, Mode::TowardsZero, negative);
        expectTop(oneToFive, Mode::Downward, positive);
        expectTop(oneToFive, Mode::Upward, negative);
        //    Rounding away from zero gives the next Number.
        expectOverflow(oneToFive, Mode::Upward, positive);
        expectOverflow(oneToFive, Mode::Downward, negative);

        // 4. Exact result from top + 5 to top + 10, past the midpoint. Rounding toward zero
        //    still gives top.
        Case const fiveToTen[] = {
            // The exact results are top + 7, top + 7, top + 6.22 and top + 9.22.
            {'+', top, Number{7'000'000'000'000'000'000, 32750}},
            {'-', top, Number{-7'000'000'000'000'000'000, 32750}},
            {'*', Number{1'000'000'000'000'000'001, 32750}, Number{Number::kMaxRep, 0}},
            {'/', top, Number{9'999'999'999'999'999'990ULL, -19, Number::Normalized{}}},
        };
        // BUG: add, subtract and divide throw "Number::normalize 1.5" in these four.
        expectTop(fiveToTen, Mode::TowardsZero, positive);
        expectTop(fiveToTen, Mode::TowardsZero, negative);
        expectTop(fiveToTen, Mode::Downward, positive);
        expectTop(fiveToTen, Mode::Upward, negative);
        //    ToNearest and rounding away from zero give the next Number.
        expectOverflow(fiveToTen, Mode::ToNearest, positive);
        expectOverflow(fiveToTen, Mode::ToNearest, negative);
        expectOverflow(fiveToTen, Mode::Upward, positive);
        expectOverflow(fiveToTen, Mode::Downward, negative);
    }

    // Add and subtract of operands at opposite ends of the exponent range are the same in the
    // model and in C++, in each rounding mode (cases from xrpld PR 7825).
    void
    testAddSubExtremeExponents()
    {
        testcase("add and subtract at extreme exponents");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);

        // (mantissa, exponentOffset): the smallest mantissa, and a mantissa near the top whose
        // round up still fits.
        std::pair<uint64_t, int> const params[] = {
            {Number::minMantissa(), 0}, {9'000'000'000'000'000'000ULL, 1}};

        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode const modeGuard{Number::setround(mode)};
            for (auto const& [mantissa, exponentOffset] : params)
            {
                auto const x = makeNumberPair(false, mantissa, Number::kMaxExponent);
                auto const y =
                    makeNumberPair(false, mantissa, Number::kMinExponent + exponentOffset);

                checkBinOp(*this, x, '+', y);
                checkBinOp(*this, x, '-', y);
                checkBinOp(*this, y, '+', x);
                checkBinOp(*this, y, '-', x);
            }
        }
    }

    // Helpers of the STAmount tests below.
    // True when an amount of the asset can be built from the mantissa.
    template <class A>
    static bool
    amountAccepted(A const& asset, std::uint64_t mantissa)
    {
        try
        {
            [[maybe_unused]] STAmount const amount{asset, mantissa};
            return true;
        }
        catch (std::exception const&)
        {
            return false;
        }
    }

    // True when adding the two amounts throws.
    static bool
    sumThrows(STAmount const& x, STAmount const& y)
    {
        try
        {
            [[maybe_unused]] STAmount const sum = x + y;
            return false;
        }
        catch (std::exception const&)
        {
            return true;
        }
    }

    // True when the text parses to an amount of the issue.
    static bool
    textAccepted(Issue const& issue, std::string const& text)
    {
        try
        {
            [[maybe_unused]] STAmount const amount = amountFromString(issue, text);
            return true;
        }
        catch (std::exception const&)
        {
            return false;
        }
    }

    // Fails with both amounts when they differ.
    void
    expectEqual(STAmount const& actual, STAmount const& expected)
    {
        BEAST_EXPECTS(actual == expected, actual.getText() + " instead of " + expected.getText());
    }

    // FV_M1_20: an STAmount built from a negative Number rounds toward zero in Downward and away
    // from zero in Upward. STAmount::fromNumber drops the sign before it rounds.
    void
    testAmountFromNegativeNumber()
    {
        testcase("FV_M1_20 STAmount from a negative Number");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        using Mode = Number::RoundingMode;
        Issue const xrp = xrpIssue();
        MPTIssue const mpt{makeMptID(1, AccountID(0x4985601))};
        Issue const usd{Currency(0x5553440000000000), AccountID(0x4985601)};

        // 1. XRP from -1.5. Rounding toward zero gives -1.
        Number const minusOneAndHalf{-15, -1};
        SaveNumberRoundMode const modeGuard{Number::setround(Mode::TowardsZero)};
        expectEqual(STAmount{xrp, minusOneAndHalf}, STAmount{xrp, 1ULL, 0, true});
        // BUG: Downward returns -1.
        Number::setround(Mode::Downward);
        expectEqual(STAmount{xrp, minusOneAndHalf}, STAmount{xrp, 2ULL, 0, true});
        // BUG: Upward returns -2.
        Number::setround(Mode::Upward);
        expectEqual(STAmount{xrp, minusOneAndHalf}, STAmount{xrp, 1ULL, 0, true});

        // 2. MPT from -1.5.
        // BUG: Downward returns -1.
        Number::setround(Mode::Downward);
        expectEqual(STAmount{mpt, minusOneAndHalf}, STAmount{mpt, 2ULL, 0, true});
        // BUG: Upward returns -2.
        Number::setround(Mode::Upward);
        expectEqual(STAmount{mpt, minusOneAndHalf}, STAmount{mpt, 1ULL, 0, true});

        // 3. IOU from -1.000000000000000001, between -1000000000000001e-15 and
        // -1000000000000000e-15.
        Number const justBelowMinusOne{-1'000'000'000'000'000'001LL, -18};
        STAmount const lower{usd, 1'000'000'000'000'001ULL, -15, true};
        STAmount const upper{usd, 1'000'000'000'000'000ULL, -15, true};
        Number::setround(Mode::TowardsZero);
        expectEqual(STAmount{usd, justBelowMinusOne}, upper);
        // BUG: Downward returns -1000000000000000e-15.
        Number::setround(Mode::Downward);
        expectEqual(STAmount{usd, justBelowMinusOne}, lower);
        // BUG: Upward returns -1000000000000001e-15.
        Number::setround(Mode::Upward);
        expectEqual(STAmount{usd, justBelowMinusOne}, upper);

        // 4. A positive Number rounds the right way.
        Number const oneAndHalf{15, -1};
        Number::setround(Mode::Downward);
        expectEqual(STAmount{xrp, oneAndHalf}, STAmount{xrp, 1ULL});
        Number::setround(Mode::Upward);
        expectEqual(STAmount{xrp, oneAndHalf}, STAmount{xrp, 2ULL});
    }

    // FV_M1_21: adding two IOU amounts in ToNearest rounds twice, to 19 digits and then to 16. It
    // can return the farther amount, and at the top of the range throw when the nearest one fits.
    void
    testIouAddRoundsTwice()
    {
        testcase("FV_M1_21 IOU add rounds twice");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        SaveNumberRoundMode const modeGuard{Number::setround(Number::RoundingMode::ToNearest)};
        Issue const usd{Currency(0x5553440000000000), AccountID(0x4985601)};

        // 1. 1000000000000001 - 0.5004 = 1000000000000000.4996, nearest amount 1000000000000000.
        STAmount const x{usd, 1'000'000'000'000'001ULL, 0};
        expectEqual(
            x - STAmount{usd, 5'004'000'000'000'000ULL, -16},
            STAmount{usd, 1'000'000'000'000'000ULL, 0});
        // 2. 1000000000000001 - 0.4996 = 1000000000000000.5004, nearest amount 1000000000000001.
        // BUG: returns 1000000000000000.
        expectEqual(x - STAmount{usd, 4'996'000'000'000'000ULL, -16}, x);

        // 3. The largest amount is 9999999999999999e80. Adding 0.5004e80 rounds to 1e96, which does
        //    not fit, so it throws.
        STAmount const largest{usd, 9'999'999'999'999'999ULL, 80};
        BEAST_EXPECT(sumThrows(largest, STAmount{usd, 5'004'000'000'000'000ULL, 64}));
        // 4. Adding 0.4996e80 rounds back to the largest amount.
        // BUG: throws "value overflow".
        STAmount const lessThanHalf{usd, 4'996'000'000'000'000ULL, 64};
        BEAST_EXPECT(!sumThrows(largest, lessThanHalf));
        if (!sumThrows(largest, lessThanHalf))
            expectEqual(largest + lessThanHalf, largest);
    }

    // FV_M1_22: an XRP or MPT amount built from a mantissa and an exponent is set to 0 when the
    // exponent is -20 or less, before rounding. The same value written two ways gives 1 or 0.
    void
    testAmountSmallExponent()
    {
        testcase("FV_M1_22 XRP and MPT amount with a small exponent");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        using Mode = Number::RoundingMode;
        Issue const xrp = xrpIssue();
        MPTIssue const mpt{makeMptID(1, AccountID(0x4985601))};

        // 1. XRP, Upward: 1e-19 rounds up to 1.
        SaveNumberRoundMode const modeGuard{Number::setround(Mode::Upward)};
        expectEqual(STAmount{xrp, 1ULL, -19}, STAmount{xrp, 1ULL});
        // BUG: the same value written as 10e-20 gives 0.
        expectEqual(STAmount{xrp, 10ULL, -20}, STAmount{xrp, 1ULL});

        // 2. XRP, Downward: -1e-19 rounds down to -1.
        Number::setround(Mode::Downward);
        expectEqual(STAmount{xrp, 1ULL, -19, true}, STAmount{xrp, 1ULL, 0, true});
        // BUG: the same value written as -10e-20 gives 0.
        expectEqual(STAmount{xrp, 10ULL, -20, true}, STAmount{xrp, 1ULL, 0, true});

        // 3. MPT, Upward: 0.18 written as 1800000000000000000e-19 rounds up to 1.
        Number::setround(Mode::Upward);
        expectEqual(STAmount{mpt, 1'800'000'000'000'000'000ULL, -19}, STAmount{mpt, 1ULL});
        // BUG: the same value written as 18000000000000000000e-20 gives 0.
        expectEqual(STAmount{mpt, 18'000'000'000'000'000'000ULL, -20}, STAmount{mpt, 1ULL});
    }

    // FV_M1_23: an MPT amount built from a mantissa of 2^63 or 2^63 + 1 becomes 9223372036854775800
    // instead of being rejected. Number::mantissa() drops the last digit of the mantissa.
    void
    testMptMantissaAboveMax()
    {
        testcase("FV_M1_23 MPT amount from a mantissa above 2^63 - 1");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        MPTIssue const mpt{makeMptID(1, AccountID(0x4985601))};

        // 1. 2^63 - 1 is the largest MPT amount.
        BEAST_EXPECT(amountAccepted(mpt, 9'223'372'036'854'775'807ULL));
        // 2. 2^63 + 2 is rejected.
        BEAST_EXPECT(!amountAccepted(mpt, 9'223'372'036'854'775'810ULL));
        // 3. 2^63 and 2^63 + 1 should be rejected as well.
        // BUG: both are accepted and become 9223372036854775800.
        BEAST_EXPECT(!amountAccepted(mpt, 9'223'372'036'854'775'808ULL));
        BEAST_EXPECT(!amountAccepted(mpt, 9'223'372'036'854'775'809ULL));
    }

    // FV_M1_24: adding two XRP amounts builds the sum with a constructor that does not call
    // canonicalize, so the sum can be above the largest XRP amount of 10^17 drops.
    void
    testXrpAddRange()
    {
        testcase("FV_M1_24 XRP add above the largest XRP amount");
        Issue const xrp = xrpIssue();
        std::uint64_t const largestDrops = 100'000'000'000'000'000ULL;

        // 1. The constructor accepts 10^17 drops and rejects 10^17 + 1.
        BEAST_EXPECT(amountAccepted(xrp, largestDrops));
        BEAST_EXPECT(!amountAccepted(xrp, largestDrops + 1));

        // 2. 10^17 + 1 should be rejected as well.
        // BUG: returns 100000000000000001.
        STAmount const largest{xrp, largestDrops};
        STAmount const one{xrp, 1ULL};
        BEAST_EXPECT(sumThrows(largest, one));

        // 3. -10^17 - 1 should be rejected.
        // BUG: returns -100000000000000001.
        BEAST_EXPECT(sumThrows(-largest, -one));
    }

    // FV_M1_25: an IOU amount built from a mantissa of 2^63 or more becomes negative. STAmount::iou
    // casts the unsigned mantissa to int64, and amountFromString and amountFromJson go through it.
    void
    testIouMantissaAboveMax()
    {
        testcase("FV_M1_25 IOU amount from a mantissa above 2^63 - 1");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        Issue const usd{Currency{0x5553440000000000}, AccountID{0x4985601}};

        // 1. 2^63 - 1 stays positive and is rounded to 16 digits.
        STAmount const rounded{usd, 9'223'372'036'854'776ULL, 3, false};
        expectEqual(STAmount{usd, 9'223'372'036'854'775'807ULL, 0, false}, rounded);

        // 2. 2^63 is one more, so it should round to the same amount.
        // BUG: the amount is -9223372036854776e3.
        expectEqual(STAmount{usd, 9'223'372'036'854'775'808ULL, 0, false}, rounded);

        // 3. A value of 19 digits, from a string and from JSON. It should round to 10^19.
        STAmount const tenToNineteen{usd, 1, 19};
        // BUG: the amount is -8446744073709552e3.
        expectEqual(amountFromString(usd, "9999999999999999999"), tenToNineteen);

        json::Value json{json::ValueType::Object};
        json[jss::currency] = "USD";
        json[jss::issuer] = toBase58(usd.account);
        json[jss::value] = "9999999999999999999";
        // BUG: the amount is -8446744073709552e3.
        expectEqual(amountFromJson(sfAmount, json), tenToNineteen);

        // 4. A value above the largest IOU amount, 9999999999999999e80, should be rejected.
        BEAST_EXPECT(!textAccepted(usd, "9999999999999999e81"));
        // BUG: it is accepted and becomes -1000000000000000e65.
        BEAST_EXPECT(!textAccepted(usd, "18446744073709551615e80"));
    }

    // FV_M1_26: adding two MPT amounts adds their int64 values with no check, so a sum above
    // 2^63 - 1 wraps around and comes back with the wrong sign.
    void
    testMptAddPastInt64()
    {
        testcase("FV_M1_26 MPT add past the largest MPT amount");
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        MPTIssue const mpt{makeMptID(1, AccountID(0x4985601))};
        std::uint64_t const largestUnits = 9'223'372'036'854'775'807ULL;

        STAmount const largest{mpt, largestUnits};
        STAmount const one{mpt, std::uint64_t{1}};
        STAmount const two{mpt, std::uint64_t{2}};
        STAmount const fiveE18{mpt, std::uint64_t{5'000'000'000'000'000'000ULL}};

        // 1. A sum of exactly 2^63 - 1 is the largest MPT amount.
        expectEqual(STAmount{mpt, largestUnits - 1} + one, largest);

        // 2. (2^63 - 1) + 2 should be rejected.
        // BUG: returns -9223372036854775807.
        BEAST_EXPECT(sumThrows(largest, two));

        // 3. 5 * 10^18 + 5 * 10^18 should be rejected.
        // BUG: returns -8446744073709551616.
        BEAST_EXPECT(sumThrows(fiveE18, fiveE18));

        // 4. -(2^63 - 1) - 2 should be rejected.
        // BUG: returns 9223372036854775807.
        BEAST_EXPECT(sumThrows(-largest, -two));
    }

    void
    runTests() override
    {
        // Open bugs. Each call fails until the C++ code is fixed, so it is commented out.
        // clang-format off
        // testMptMulRatioUnderflow();      // FV_M1_11
        // testTopExponentOverflow();       // FV_M1_19
        // testAmountFromNegativeNumber();  // FV_M1_20
        // testIouAddRoundsTwice();         // FV_M1_21
        // testAmountSmallExponent();       // FV_M1_22
        // testMptMantissaAboveMax();       // FV_M1_23
        // testXrpAddRange();               // FV_M1_24
        // testIouMantissaAboveMax();       // FV_M1_25
        // testMptAddPastInt64();           // FV_M1_26

        // Cases that pass today, kept as regression tests.
        testRangeBoundaryArithmetic();      // FV_M1_12
        testMultiplicationRounding();       // FV_M1_12
        testCuspRounding();                 // FV_M1_12
        testDivisionRounding();             // FV_M1_13
        testLargeGapAddSub();               // FV_M1_14
        testNegativeComparison();           // FV_M1_15
        testAddDirectedRounding();          // FV_M1_16
        testAddToNearestCancellation();     // FV_M1_17

        // Cases with no bug ID, kept as regression tests.
        testAddSubExtremeExponents();
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(NumberFindings, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
