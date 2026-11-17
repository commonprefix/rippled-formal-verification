#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/BoolFFI.h>
#include <test/formal_verification/ffi/Int64FFI.h>
#include <test/formal_verification/ffi/protocol/IOUAmountFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberHelpers.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Feature.h>
#include <xrpl/protocol/IOUAmount.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/MPTAmount.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Rules.h>
#include <xrpl/protocol/STAmount.h>

#include <cstddef>
#include <cstdint>
#include <exception>
#include <initializer_list>
#include <limits>
#include <optional>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_set>

extern "C" {
lean_object*
lean_st_amount_build(lean_object* numericType, uint64_t mantissa, int64_t offset, uint8_t negative);
lean_object*
lean_stamount_int_amount(lean_object*);
lean_object*
lean_stamount_iou(lean_object*, uint8_t);
lean_object*
lean_stamount_to_number(lean_object*, uint8_t);
lean_object*
lean_stamount_checked(lean_object*, uint64_t, int64_t, uint8_t, uint8_t);
lean_object*
lean_stamount_of_number(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_lt(lean_object*, lean_object*);
lean_object*
lean_stamount_add(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_sub(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_round_to_exponent(lean_object*, int64_t, uint8_t);
lean_object*
lean_stamount_neg(lean_object*);
lean_object*
lean_stamount_unchecked_from_int64(lean_object*, int64_t, int64_t);
uint8_t
lean_stamount_eq(lean_object*, lean_object*);
lean_object*
lean_stamount_le(lean_object*, lean_object*);
lean_object*
lean_stamount_gt(lean_object*, lean_object*);
uint8_t
lean_stamount_are_comparable(lean_object*, lean_object*);
}

namespace xrpl::test {

using namespace formal_verification;

namespace {

// 3-way model tag from the asset: native (0) / int64 for MPT (1) / fractional for IOU (2).
uint8_t
numericTypeFromAsset(STAmount const& s)
{
    return s.native() ? kNative : s.asset().holds<MPTIssue>() ? kIntegral : kFractional;
}

bool
stAmountFieldsEqual(LeanSTAmountResult const& lean, STAmount const& cpp)
{
    bool const cppIntegral = numericTypeFromAsset(cpp) != kFractional;
    return (lean.numericType != 0) == cppIntegral && lean.mValue == cpp.mantissa() &&
        lean.mOffset == cpp.exponent() && (lean.isNegative != 0) == cpp.negative();
}

// Signed drops of raw STAmount fields as int64, or nullopt when they leave the int64 range.
// C++ casts mValue to int64 without a check there, the model reports `Error.wrap`.
std::optional<int64_t>
signedDrops(uint64_t mValue, bool negative)
{
    constexpr auto kInt64Max = static_cast<uint64_t>(std::numeric_limits<int64_t>::max());
    if (mValue <= kInt64Max)
        return negative ? -static_cast<int64_t>(mValue) : static_cast<int64_t>(mValue);
    if (negative && mValue == kInt64Max + 1)
        return std::numeric_limits<int64_t>::min();
    return std::nullopt;
}

// Whether the model's IOU add (sub negates b first) reports `Error.wrap`: an operand's mantissa
// leaves int64. C++ wraps it silently.
bool
addWraps(STAmountPair const& a, STAmountPair const& b, bool isAdd)
{
    auto const& x = a.leanSt;
    auto const& y = b.leanSt;
    if (x.numericType != y.numericType || y.mValue == 0)
        return false;
    bool const yNegative = (y.isNegative != 0) == isAdd;
    auto const dy = signedDrops(y.mValue, yNegative);
    // A zero left operand re-canonicalizes the right one, which reads IOU drops as int64.
    if (x.mValue == 0)
        return x.numericType == kFractional && !dy;
    auto const dx = signedDrops(x.mValue, x.isNegative != 0);
    return !dx || !dy;
}

// Raw STAmount fields for the checked constructor.
struct CheckedCase
{
    bool negative;
    std::uint64_t mantissa;
    int exponent;
    TER expected;
    std::optional<Number::RoundingMode> mode{};
};

// A Number mantissa * 10^exponent, as ToNearest stores it.
struct OfNumberCase
{
    std::int64_t mantissa;
    int exponent;
    TER expected;
    std::optional<Number::RoundingMode> mode{};
};

// Two IOU mantissas at one exponent.
struct PairCase
{
    std::int64_t a;
    std::int64_t b;
    int exponent;
    TER expected;
};

// An IOU mantissa * 10^exponent rounded to scale, and the amount C++ returns.
struct RoundToScaleCase
{
    std::int64_t mantissa;
    int exponent;
    int scale;
    ScaledValue expected;
    std::optional<Number::RoundingMode> mode{};
};

std::string
text(CheckedCase const& c, Number::RoundingMode mode)
{
    return (c.negative ? "-" : "") + std::to_string(c.mantissa) + "e" + std::to_string(c.exponent) +
        ", " + modeName(mode);
}

std::string
text(OfNumberCase const& c, Number::RoundingMode mode)
{
    return std::to_string(c.mantissa) + "e" + std::to_string(c.exponent) + ", " + modeName(mode);
}

std::string
text(PairCase const& c, char op, Number::RoundingMode mode)
{
    return std::to_string(c.a) + ' ' + op + ' ' + std::to_string(c.b) + " at exponent " +
        std::to_string(c.exponent) + ", " + modeName(mode);
}

std::string
text(RoundToScaleCase const& c, Number::RoundingMode mode)
{
    return std::to_string(c.mantissa) + "e" + std::to_string(c.exponent) + " to scale " +
        std::to_string(c.scale) + ", " + modeName(mode);
}

}  // namespace

class LeanSTAmount_test : public LeanSuite
{
    static std::string
    label(char const* op, uint8_t nt, uint64_t mValue, int64_t mOffset, uint8_t isNeg)
    {
        std::stringstream ss;
        ss << op << "(nt=" << static_cast<int>(nt) << "," << (isNeg ? "-" : "+") << mValue << "e"
           << mOffset << ")";
        return ss.str();
    }

    // Compares both sides; returns the C++ verdict.
    TER
    checkStAmountResult(
        std::string const& tag,
        LeanSTAmountResult const& lean,
        STAmount const& cpp,
        bool cppThrew)
    {
        TER const verdict = cppVerdict(cppThrew, !cppThrew && cpp.signum() == 0);
        if (lean.ok == cppThrew)
        {
            std::stringstream ss;
            ss << tag << ": error mismatch lean.ok=" << lean.ok << " cppThrew=" << cppThrew;
            fail(ss.str());
            return verdict;
        }
        if (!lean.ok)
        {
            pass();
            return verdict;
        }
        if (!stAmountFieldsEqual(lean, cpp))
        {
            std::stringstream ss;
            ss << tag << ": value mismatch lean=" << format(lean) << " cpp=" << format(cpp);
            fail(ss.str());
            return verdict;
        }
        pass();
        return verdict;
    }

    template <typename CppFn>
    TER
    runSTAmountOp(std::string const& tag, LeanSTAmountResult const& lean, CppFn&& cppFn)
    {
        STAmount cpp;
        bool cppThrew = false;
        try
        {
            cpp = cppFn();
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        return checkStAmountResult(tag, lean, cpp, cppThrew);
    }

    // Where C++ wraps an int64 silently the model reports `Error.wrap`, so there is no C++ value
    // to compare against.
    bool
    expectWrap(std::string const& tag, std::optional<LeanError> const& error)
    {
        if (error != LeanError::wrap)
        {
            fail(tag + ": expected the model to report a wrap");
            return false;
        }
        pass();
        return true;
    }

    bool
    checkAccessors(STAmountPair const& p, Number::RoundingMode mode)
    {
        uint8_t const nt = p.leanSt.numericType;
        uint64_t const mValue = p.leanSt.mValue;
        int64_t const mOffset = p.leanSt.mOffset;
        uint8_t const isNeg = p.leanSt.isNegative;
        STAmount const& cpp = p.cppSt;
        std::string const tag = label("accessor", nt, mValue, mOffset, isNeg);
        uint8_t const leanMode = toLeanMode(mode);
        bool ok = true;

        // intAmount (integral) or iou (fractional) reads the drops, and toNumber reads them too.
        if (!signedDrops(mValue, isNeg != 0))
        {
            auto const build = [&] { return STAmountFFI::build(nt, mValue, mOffset, isNeg); };
            if (nt == kFractional)
            {
                auto const iou =
                    readExcept<IOUAmountFFI>(leanCall(lean_stamount_iou, build(), leanMode));
                ok &= expectWrap(tag + ".iou", iou.error);
            }
            else
            {
                auto const drops =
                    readExcept<Int64FFI>(leanCall(lean_stamount_int_amount, build()));
                ok &= expectWrap(tag + ".intAmount", drops.error);
            }
            auto const number =
                readExcept<NumberFFI>(leanCall(lean_stamount_to_number, build(), leanMode));
            ok &= expectWrap(tag + ".toNumber", number.error);
            return ok;
        }

        {
            auto lean = readExcept<Int64FFI>(
                leanCall(lean_stamount_int_amount, STAmountFFI::build(nt, mValue, mOffset, isNeg)));
            bool cppThrew = false;
            int64_t cppVal = 0;
            try
            {
                cppVal = cpp.mpt().value();
            }
            catch (std::exception const&)
            {
                cppThrew = true;
            }
            if (lean.value.has_value() == cppThrew)
            {
                fail(tag + ".intAmount: error mismatch");
                ok = false;
            }
            else if (lean.value.has_value() && lean.value->read() != cppVal)
            {
                fail(tag + ".intAmount: value mismatch");
                ok = false;
            }
            else
                pass();
        }
        {
            NumberRoundModeGuard mg(mode);
            auto lean = IOUAmountFFI::fromExcept(leanCall(
                lean_stamount_iou, STAmountFFI::build(nt, mValue, mOffset, isNeg), leanMode));
            bool cppThrew = false;
            IOUAmount cppIou;
            try
            {
                cppIou = cpp.iou();
            }
            catch (std::exception const&)
            {
                cppThrew = true;
            }
            if (lean.ok == cppThrew)
            {
                fail(tag + ".iou: error mismatch");
                ok = false;
            }
            else if (
                lean.ok &&
                (lean.mantissa != cppIou.mantissa() || lean.exponent != cppIou.exponent()))
            {
                fail(tag + ".iou: value mismatch");
                ok = false;
            }
            else
                pass();
        }
        {
            NumberRoundModeGuard mg(mode);
            auto lean = NumberFFI::fromExcept(leanCall(
                lean_stamount_to_number, STAmountFFI::build(nt, mValue, mOffset, isNeg), leanMode));
            bool cppThrew = false;
            Number cppN;
            try
            {
                cppN = static_cast<Number>(cpp);
            }
            catch (std::exception const&)
            {
                cppThrew = true;
            }
            if (lean.ok == cppThrew)
            {
                fail(tag + ".toNumber: error mismatch");
                ok = false;
            }
            else if (lean.ok && !fieldsEqual(lean, cppN))
            {
                std::stringstream ss;
                ss << tag << ".toNumber: mismatch lean=" << format(lean) << " cpp=" << format(cppN);
                fail(ss.str());
                ok = false;
            }
            else
                pass();
        }
        return ok;
    }

    TER
    checkChecked(STAmountPair const& p, Number::RoundingMode mode)
    {
        auto const& s = p.leanSt;
        NumberRoundModeGuard mg(mode);
        // Use the checked ctor to match Lean's error path.
        return runSTAmountOp(
            label("checked", s.numericType, s.mValue, s.mOffset, s.isNegative),
            STAmountFFI::fromExcept(leanCall(
                lean_stamount_checked,
                NumericTypeFFI::build(s.numericType),
                s.mValue,
                s.mOffset,
                s.isNegative,
                toLeanMode(mode))),
            [&] {
                return STAmount{
                    assetForNumericType(s.numericType),
                    s.mValue,
                    static_cast<int>(s.mOffset),
                    s.isNegative != 0};
            });
    }

    TER
    checkAddSub(
        char const* op,
        bool isAdd,
        STAmountPair const& a,
        STAmountPair const& b,
        Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        auto leanFn = isAdd ? lean_stamount_add : lean_stamount_sub;
        std::stringstream tag;
        tag << op << "(nt1=" << static_cast<int>(a.leanSt.numericType)
            << ",nt2=" << static_cast<int>(b.leanSt.numericType) << ")";
        lean_object* const lean = leanCall(
            leanFn,
            STAmountFFI::build(
                a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
            STAmountFFI::build(
                b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative),
            toLeanMode(mode));
        if (addWraps(a, b, isAdd))
        {
            expectWrap(tag.str(), readExcept<STAmountFFI>(lean).error);
            return tesSUCCESS;  // C++ returns the wrapped value.
        }
        return runSTAmountOp(tag.str(), STAmountFFI::fromExcept(lean), [&] {
            return isAdd ? (a.cppSt + b.cppSt) : (a.cppSt - b.cppSt);
        });
    }

    TER
    checkRoundToExponent(STAmountPair const& p, int32_t scale, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        std::stringstream tag;
        tag << "roundToExponent(nt=" << static_cast<int>(p.leanSt.numericType) << ",scale=" << scale
            << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                lean_stamount_round_to_exponent,
                STAmountFFI::build(
                    p.leanSt.numericType, p.leanSt.mValue, p.leanSt.mOffset, p.leanSt.isNegative),
                scale,
                toLeanMode(mode))),
            [&] { return roundToScale(p.cppSt, scale, mode); });
    }

    bool
    expectBool(char const* op, uint8_t lean, bool cpp)
    {
        if ((lean != 0) != cpp)
        {
            std::stringstream ss;
            ss << op << ": lean=" << (lean != 0) << " cpp=" << cpp;
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    bool
    checkEq(STAmountPair const& a, STAmountPair const& b)
    {
        return expectBool(
            "eq",
            leanCall(
                lean_stamount_eq,
                STAmountFFI::build(
                    a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
                STAmountFFI::build(
                    b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative)),
            a.cppSt == b.cppSt);
    }

    bool
    checkOrdering(
        char const* op,
        lean_object* (*leanFn)(lean_object*, lean_object*),
        bool cppRet,
        bool cppThrew,
        STAmountPair const& a,
        STAmountPair const& b)
    {
        auto lean = readExcept<BoolFFI>(leanCall(
            leanFn,
            STAmountFFI::build(
                a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
            STAmountFFI::build(
                b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative)));
        std::stringstream tag;
        tag << op << "(nt1=" << static_cast<int>(a.leanSt.numericType)
            << ",nt2=" << static_cast<int>(b.leanSt.numericType) << ")";
        if (lean.value.has_value() == cppThrew)
        {
            fail(tag.str() + ": error mismatch");
            return false;
        }
        if (lean.value.has_value() && lean.value->read() != cppRet)
        {
            fail(tag.str() + ": value mismatch");
            return false;
        }
        pass();
        return true;
    }

    bool
    checkLt(STAmountPair const& a, STAmountPair const& b)
    {
        bool cpp = false, cppThrew = false;
        try
        {
            cpp = a.cppSt < b.cppSt;
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        return checkOrdering("lt", lean_stamount_lt, cpp, cppThrew, a, b);
    }

    bool
    checkLe(STAmountPair const& a, STAmountPair const& b)
    {
        bool cpp = false, cppThrew = false;
        try
        {
            cpp = a.cppSt <= b.cppSt;
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        return checkOrdering("le", lean_stamount_le, cpp, cppThrew, a, b);
    }

    bool
    checkGt(STAmountPair const& a, STAmountPair const& b)
    {
        bool cpp = false, cppThrew = false;
        try
        {
            cpp = a.cppSt > b.cppSt;
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        return checkOrdering("gt", lean_stamount_gt, cpp, cppThrew, a, b);
    }

    bool
    checkAreComparable(STAmountPair const& a, STAmountPair const& b)
    {
        // For the sentinel assets, comparability reduces to matching numericType.
        return expectBool(
            "areComparable",
            leanCall(
                lean_stamount_are_comparable,
                STAmountFFI::build(
                    a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
                STAmountFFI::build(
                    b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative)),
            a.leanSt.numericType == b.leanSt.numericType);
    }

    TER
    checkNeg(STAmountPair const& p)
    {
        auto const& s = p.leanSt;
        return runSTAmountOp(
            label("neg", s.numericType, s.mValue, s.mOffset, s.isNegative),
            STAmountFFI::fromObject(leanCall(
                lean_stamount_neg,
                STAmountFFI::build(s.numericType, s.mValue, s.mOffset, s.isNegative))),
            [&] { return -p.cppSt; });
    }

    TER
    checkUncheckedFromInt64(uint8_t nt, int64_t v, int64_t offset)
    {
        bool const neg = v < 0;
        std::stringstream tag;
        tag << "uncheckedFromInt64(nt=" << static_cast<int>(nt) << "," << v << "e" << offset << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromObject(
                leanCall(lean_stamount_unchecked_from_int64, NumericTypeFFI::build(nt), v, offset)),
            [&] { return stAmountUnchecked(nt, magnitude(v), offset, neg ? 1 : 0); });
    }

    TER
    checkOfNumber(uint8_t nt, NumberPair const& n, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        std::stringstream tag;
        tag << "ofNumber(nt=" << static_cast<int>(nt) << "," << (n.leanNum.negative ? "-" : "+")
            << n.leanNum.mantissa << "e" << n.cppNum.exponent() << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                lean_stamount_of_number,
                NumericTypeFFI::build(nt),
                lean_number_build(
                    n.leanNum.negative,
                    n.leanNum.mantissa,
                    static_cast<int64_t>(n.leanNum.exponent)),
                toLeanMode(mode))),
            [&] {
                return assetForNumericType(nt).visit(
                    [&](Issue const& iss) { return STAmount{iss, n.cppNum}; },
                    [&](MPTIssue const& mpt) { return STAmount{mpt, n.cppNum}; });
            });
    }

public:
    void
    test_known_construction()
    {
        beginCase("LeanSTAmount.known_construction");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;

        constexpr uint64_t kMin = STAmount::kMinValue;
        constexpr uint64_t kMax = STAmount::kMaxValue;
        constexpr int eMin = STAmount::kMinOffset;
        constexpr int eMax = STAmount::kMaxOffset;
        // int64 (MPT) ceiling = INT64_MAX; native (XRP) ceiling = 10^17, offset 17.
        constexpr uint64_t kMaxIntegral =
            static_cast<uint64_t>(std::numeric_limits<int64_t>::max());
        constexpr uint64_t kMaxNative = 100'000'000'000'000'000ULL;

        for (auto mode : kRoundingModes)
        {
            checkAccessors(makeSTAmountPair(kIntegral, 0, 0, 0), mode);
            checkAccessors(makeSTAmountPair(kIntegral, 1, 0, 0), mode);
            checkAccessors(makeSTAmountPair(kIntegral, 1, 0, 1), mode);
            checkAccessors(makeSTAmountPair(kIntegral, 1'000, 0, 0), mode);
            checkAccessors(makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0), mode);

            checkAccessors(makeSTAmountPair(kFractional, 0, -100, 0), mode);
            checkAccessors(makeSTAmountPair(kFractional, kMin, 0, 0), mode);
            checkAccessors(makeSTAmountPair(kFractional, kMax, eMax, 0), mode);
            checkAccessors(makeSTAmountPair(kFractional, kMin, eMin, 1), mode);
        }

        // checked ctor: in-range happy paths per numericType.
        checkChecked(makeSTAmountPair(kIntegral, 1'000, 0, 0), m);
        checkChecked(makeSTAmountPair(kIntegral, 0, 0, 0), m);
        checkChecked(makeSTAmountPair(kIntegral, 1'000'000'000ULL, 0, 0), m);
        checkChecked(makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0), m);
        // native (XRP): in-range, at 10^17 via mantissa and via offset 17.
        checkChecked(makeSTAmountPair(kNative, 1'000'000, 0, 0), m);
        checkChecked(makeSTAmountPair(kNative, kMaxNative, 0, 0), m);
        checkChecked(makeSTAmountPair(kNative, 1, 17, 0), m);
        checkChecked(makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0), m);
        checkChecked(makeSTAmountPair(kFractional, 0, 0, 0), m);
        checkChecked(makeSTAmountPair(kFractional, 1, 0, 0), m);
        checkChecked(makeSTAmountPair(kFractional, kMax, eMax, 0), m);
        checkChecked(makeSTAmountPair(kFractional, kMin, eMin, 0), m);

        // Unchecked-from-int64 entry: STAmount stores raw fields without
        // canonicalization. Cover each numericType with zero, ±1, and semantic
        // extremes. Out-of-range field extremes live in test_extreme_values.
        for (uint8_t nt : {kIntegral, kFractional})
        {
            checkUncheckedFromInt64(nt, 0, 0);
            checkUncheckedFromInt64(nt, 1, 0);
            checkUncheckedFromInt64(nt, -1, 0);
        }
        checkUncheckedFromInt64(kIntegral, static_cast<int64_t>(kMaxIntegral), 0);
        checkUncheckedFromInt64(kIntegral, -static_cast<int64_t>(kMaxIntegral), 0);
        checkUncheckedFromInt64(kNative, static_cast<int64_t>(kMaxNative), 0);
        checkUncheckedFromInt64(kNative, -static_cast<int64_t>(kMaxNative), 0);
        checkUncheckedFromInt64(kFractional, static_cast<int64_t>(kMin), eMin);
        checkUncheckedFromInt64(kFractional, static_cast<int64_t>(kMax), eMax);
        checkUncheckedFromInt64(kFractional, -static_cast<int64_t>(kMax), eMax);

        for (auto nt : {kIntegral, kFractional})
        {
            for (auto [neg, mant, exp_] :
                 std::initializer_list<std::tuple<uint8_t, uint64_t, int64_t>>{
                     {0, 0, 0},
                     {0, 1'000'000'000'000'000'000ULL, 0},
                     {1, 1'000'000'000'000'000'000ULL, 0},
                     {0, 1'234'567'890'123'456'789ULL, -2}})
            {
                checkOfNumber(nt, makeNumberPair(neg != 0, mant, static_cast<int>(exp_)), m);
            }
        }
    }

    void
    test_known_comparison()
    {
        beginCase("LeanSTAmount.known_comparison");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        checkLt(makeSTAmountPair(kIntegral, 1, 0, 0), makeSTAmountPair(kIntegral, 2, 0, 0));
        checkLt(makeSTAmountPair(kIntegral, 2, 0, 0), makeSTAmountPair(kIntegral, 1, 0, 0));
        checkLt(makeSTAmountPair(kIntegral, 1, 0, 1), makeSTAmountPair(kIntegral, 1, 0, 0));
        checkLt(makeSTAmountPair(kIntegral, 100, 0, 0), makeSTAmountPair(kIntegral, 200, 0, 0));
        checkLt(makeSTAmountPair(kIntegral, 100, 0, 0), makeSTAmountPair(kIntegral, 100, 0, 0));
        checkLt(
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 1, 0));
        checkLt(
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 5'000'000'000'000'001ULL, 0, 0));
        checkLt(
            makeSTAmountPair(kFractional, 0, -100, 0),
            makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0));
        // Cross-type (integral vs fractional) is incomparable: C++ throws, Lean errors.
        checkLt(
            makeSTAmountPair(kIntegral, 100, 0, 0),
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0));
        checkLt(
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kIntegral, 100, 0, 0));
    }

    void
    test_known_arithmetic()
    {
        beginCase("LeanSTAmount.known_arithmetic");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;

        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
            m);
        checkAddSub(
            "sub",
            false,
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
            m);
        // Cross-type add/sub must error on both sides.
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kIntegral, 1'000, 0, 0),
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            m);
        checkAddSub(
            "sub",
            false,
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kIntegral, 1'000, 0, 0),
            m);

        // Every mode on a non-trivial IOU sum.
        for (auto mode : kRoundingModes)
        {
            checkAddSub(
                "add",
                true,
                makeSTAmountPair(kFractional, 1'234'567'890'123'456ULL, 0, 0),
                makeSTAmountPair(kFractional, 9'876'543'210'987'654ULL, -3, 1),
                mode);
        }
    }

    void
    test_known_round_to_exponent()
    {
        beginCase("LeanSTAmount.known_round_to_exponent");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);

        // integral / fractional-zero: no-op short-circuits.
        checkRoundToExponent(
            makeSTAmountPair(kIntegral, 1'000, 0, 0), 0, Number::RoundingMode::ToNearest);
        checkRoundToExponent(
            makeSTAmountPair(kFractional, 0, -100, 0), 0, Number::RoundingMode::ToNearest);
        // IOU exponent >= scale: no-op.
        checkRoundToExponent(
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            -1,
            Number::RoundingMode::ToNearest);
        // Scale equal to exponent: no-op (boundary).
        checkRoundToExponent(
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, -5, 0),
            -5,
            Number::RoundingMode::ToNearest);
        // IOU exponent < scale: rounds via the add-then-sub trick.
        for (auto mode : kRoundingModes)
        {
            checkRoundToExponent(
                makeSTAmountPair(kFractional, 1'234'567'890'123'456ULL, -10, 0), -5, mode);
            checkRoundToExponent(
                makeSTAmountPair(kFractional, 1'234'567'890'123'456ULL, -10, 1), -5, mode);
        }
    }

    void
    test_fuzz_accessors()
    {
        beginCase("LeanSTAmount.fuzz_accessors", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(5'000, [&] { return checkAccessors(randomSTAmountPair(rng), mode); });
        }
    }

    void
    test_fuzz_constructors()
    {
        beginCase("LeanSTAmount.fuzz_constructors", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            // checked: hits canonicalization + boundary errors per numericType.
            runFuzz(10'000, [&] { return checkChecked(randomSTAmountPair(rng), mode); });
        }
    }

    void
    test_fuzz_add_sub()
    {
        beginCase("LeanSTAmount.fuzz_add_sub", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            std::bernoulli_distribution opDist(0.5);
            runFuzz(10'000, [&] {
                bool const isAdd = opDist(rng);
                auto a = randomSTAmountPair(rng, kFractional);
                auto b = randomSTAmountPair(rng, kFractional);
                return checkAddSub(isAdd ? "add" : "sub", isAdd, a, b, mode);
            });
        }
    }

    void
    test_fuzz_round_to_exponent()
    {
        beginCase("LeanSTAmount.fuzz_round_to_exponent", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        std::uniform_int_distribution<int32_t> scaleDist(-110, 10);
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(10'000, [&] {
                auto p = randomSTAmountPair(rng);
                int32_t const scale = scaleDist(rng);
                return checkRoundToExponent(p, scale, mode);
            });
        }
    }

    void
    test_fuzz_compare()
    {
        beginCase("LeanSTAmount.fuzz_compare", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        runFuzz(20'000, [&] {
            auto a = randomSTAmountPair(rng);
            auto b = randomSTAmountPair(rng);
            bool ok = true;
            ok &= checkEq(a, b);
            ok &= checkLt(a, b);
            ok &= checkLe(a, b);
            ok &= checkGt(a, b);
            ok &= checkAreComparable(a, b);
            return ok;
        });
    }

    void
    test_fuzz_neg()
    {
        beginCase("LeanSTAmount.fuzz_neg", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        runFuzz(20'000, [&] { return checkNeg(randomSTAmountPair(rng)); });
    }

    void
    test_fuzz_unchecked_from_int64()
    {
        beginCase("LeanSTAmount.fuzz_unchecked_from_int64", true);
        auto& rng = nextRng();
        std::uniform_int_distribution<int64_t> vDist(
            std::numeric_limits<int64_t>::min(), std::numeric_limits<int64_t>::max());
        std::uniform_int_distribution<int64_t> offDist(-100, 100);
        runFuzz(20'000, [&] {
            uint8_t const nt = randomNumericType(rng);
            int64_t const v = vDist(rng);
            int64_t const off = offDist(rng);
            return checkUncheckedFromInt64(nt, v, off);
        });
    }

    void
    test_extreme_values()
    {
        beginCase("LeanSTAmount.extreme_values");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;

        // int64 (MPT) ceiling is INT64_MAX (== kMaxMpTokenAmount); native (XRP) ceiling is 10^17.
        constexpr uint64_t kMaxIntegral =
            static_cast<uint64_t>(std::numeric_limits<int64_t>::max());
        constexpr uint64_t kMaxNative = 100'000'000'000'000'000ULL;
        constexpr uint64_t iouMax = static_cast<uint64_t>(STAmount::kMaxValue);
        constexpr uint64_t iouMin = static_cast<uint64_t>(STAmount::kMinValue);
        constexpr int64_t eMax = STAmount::kMaxOffset;
        constexpr int64_t eMin = STAmount::kMinOffset;

        // checked ctor at the out-of-range corners — both sides must error.
        checkChecked(makeSTAmountPair(kIntegral, kMaxIntegral + 1, 0, 0), m);
        checkChecked(makeSTAmountPair(kIntegral, 1, 19, 0), m);
        checkChecked(makeSTAmountPair(kFractional, iouMax, eMax + 1, 0), m);
        checkChecked(makeSTAmountPair(kFractional, iouMin, eMin - 1, 0), m);

        // native (XRP) ceiling is 10^17, well under INT64_MAX: exactly max is ok, and each of
        // (max+1), an int64-max mantissa (valid for MPT), and offset 18 must error on both sides.
        checkChecked(makeSTAmountPair(kNative, kMaxNative, 0, 0), m);
        checkChecked(makeSTAmountPair(kNative, kMaxNative + 1, 0, 0), m);
        checkChecked(makeSTAmountPair(kNative, kMaxIntegral, 0, 0), m);
        checkChecked(makeSTAmountPair(kNative, 1, 18, 0), m);
        // neg is sign-magnitude and never overflows.
        checkNeg(makeSTAmountPair(kNative, kMaxNative, 0, 0));
        checkNeg(makeSTAmountPair(kNative, kMaxNative, 0, 1));
        // Cross-kind native vs int64 (MPT) is incomparable: both sides error.
        checkLt(makeSTAmountPair(kNative, 100, 0, 0), makeSTAmountPair(kIntegral, 100, 0, 0));

        // IOU exponent overflow at kMaxOffset; smallest ± smallest at kMinOffset.
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kFractional, iouMax, eMax, 0),
            makeSTAmountPair(kFractional, iouMax, eMax, 0),
            m);
        checkAddSub(
            "sub",
            false,
            makeSTAmountPair(kFractional, iouMax, eMax, 0),
            makeSTAmountPair(kFractional, iouMax, eMax, 1),
            m);
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kFractional, iouMin, eMin, 0),
            makeSTAmountPair(kFractional, iouMin, eMin, 1),
            m);

        // neg is sign-magnitude → never overflows.
        checkNeg(makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0));
        checkNeg(makeSTAmountPair(kIntegral, kMaxIntegral, 0, 1));
        checkNeg(makeSTAmountPair(kFractional, iouMax, eMax, 0));

        // Cross-type compare → error; same-type ordering -max < +max.
        checkLt(
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0),
            makeSTAmountPair(kFractional, iouMax, eMax, 0));
        checkLt(
            makeSTAmountPair(kFractional, iouMax, eMax, 1),
            makeSTAmountPair(kFractional, iouMax, eMax, 0));

        // Raw field extremes via the Unchecked path: both sides decode these
        // verbatim, so we see how each operation copes at the field limits.
        constexpr uint64_t u64Max = std::numeric_limits<uint64_t>::max();
        constexpr int64_t intMax = std::numeric_limits<int>::max();
        constexpr int64_t intMin = std::numeric_limits<int>::min();
        for (uint8_t neg : {uint8_t{0}, uint8_t{1}})
        {
            for (uint8_t nt : {kIntegral, kFractional})
            {
                checkNeg(makeSTAmountPair(nt, u64Max, 0, neg));
                checkNeg(makeSTAmountPair(nt, 0, 0, neg));
                checkLt(makeSTAmountPair(nt, u64Max, 0, neg), makeSTAmountPair(nt, 0, 0, neg));
            }
            // C++ reads u64Max back as int64 (iou() gives -1), the model reports the wrap.
            checkAddSub(
                "add",
                true,
                makeSTAmountPair(kFractional, u64Max, 0, neg),
                makeSTAmountPair(kFractional, u64Max, 0, neg),
                m);
            // Fractional additionally spans the int-exponent extremes (Number-mediated
            // out-of-range offsets surface as errors on both sides).
            checkNeg(makeSTAmountPair(kFractional, u64Max, intMax, neg));
            checkNeg(makeSTAmountPair(kFractional, u64Max, intMin, neg));
            checkAddSub(
                "add",
                true,
                makeSTAmountPair(kFractional, u64Max, intMax, neg),
                makeSTAmountPair(kFractional, 1, intMin, neg),
                m);
            checkLt(
                makeSTAmountPair(kFractional, u64Max, intMax, neg),
                makeSTAmountPair(kFractional, u64Max, intMin, neg));
        }
    }

    // Integral values staged above INT64_MAX: C++ reads them back as int64 via mpt()/getMPTValue
    // (u64Max -> -1), the model reports the wrap from intAmount and toNumber.
    void
    test_integral_int64_wrap()
    {
        beginCase("LeanSTAmount.integral_int64_wrap");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;
        constexpr uint64_t u64Max = std::numeric_limits<uint64_t>::max();

        checkAccessors(makeSTAmountPair(kIntegral, u64Max, 0, 0), m);
    }

    // Finding (FV_M2_1): XRP operator+ adds one drop to an INT64_MAX wraps to INT64_MIN, no guard.
    void
    test_add_xrp_overflow()
    {
        beginCase("LeanSTAmount.add_xrp_overflow");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;

        constexpr uint64_t kIntMax = static_cast<uint64_t>(std::numeric_limits<int64_t>::max());
        STAmountPair const a = makeSTAmountPair(kNative, kIntMax, 0, 0);  // INT64_MAX drops
        STAmountPair const b = makeSTAmountPair(kNative, 1, 0, 0);        // + 1 drop

        bool cppThrew = false;
        STAmount cppSum;
        try
        {
            cppSum = a.cppSt + b.cppSt;
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }

        NumberRoundModeGuard mg(m);
        auto const lean = STAmountFFI::fromExcept(leanCall(
            lean_stamount_add,
            STAmountFFI::build(
                a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
            STAmountFFI::build(
                b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative),
            toLeanMode(m)));

        BEAST_EXPECTS(
            cppThrew || cppSum.signum() > 0,
            "C++ XRP add at INT64_MAX wrapped to a negative value");
        BEAST_EXPECTS(
            !lean.ok || lean.isNegative == 0,
            "Lean XRP add at INT64_MAX wrapped to a negative value");
    }

    static STAmountPair
    iouPair(std::int64_t mantissa, std::int64_t exponent)
    {
        return makeSTAmountPair(kFractional, magnitude(mantissa), exponent, mantissa < 0 ? 1 : 0);
    }

    // One test case per list; each row compares Lean with C++, then the C++ result with the row.
    void
    testBoundaries()
    {
        auto const checked = [&](std::uint8_t nt) {
            return [&, nt](std::size_t i, CheckedCase const& c, Number::RoundingMode mode) {
                auto const p = makeSTAmountPair(nt, c.mantissa, c.exponent, c.negative ? 1 : 0);
                expectResult(i, text(c, mode), checkChecked(p, mode), c.expected);
            };
        };
        auto const ofNumber = [&](std::uint8_t nt) {
            return [&, nt](std::size_t i, OfNumberCase const& c, Number::RoundingMode mode) {
                expectResult(
                    i,
                    text(c, mode),
                    checkOfNumber(nt, storedNumber(c.mantissa, c.exponent), mode),
                    c.expected);
            };
        };
        auto const add = [&](std::size_t i, PairCase const& c, Number::RoundingMode mode) {
            TER const verdict =
                checkAddSub("add", true, iouPair(c.a, c.exponent), iouPair(c.b, c.exponent), mode);
            expectResult(i, text(c, '+', mode), verdict, c.expected);
        };
        auto const sub = [&](std::size_t i, PairCase const& c, Number::RoundingMode mode) {
            TER const verdict =
                checkAddSub("sub", false, iouPair(c.a, c.exponent), iouPair(c.b, c.exponent), mode);
            expectResult(i, text(c, '-', mode), verdict, c.expected);
        };
        auto const rounded =
            [&](std::size_t i, RoundToScaleCase const& c, Number::RoundingMode mode) {
                auto const p = iouPair(c.mantissa, c.exponent);
                checkRoundToExponent(p, c.scale, mode);
                STAmount const r = roundToScale(p.cppSt, c.scale, mode);
                auto const m = static_cast<std::int64_t>(r.mantissa());
                expectResult(
                    i, text(c, mode), ScaledValue{r.negative() ? -m : m, r.exponent()}, c.expected);
            };

        runRows(*this, "LeanSTAmount.checked XRP", kCheckedXrp, checked(kNative));
        runRows(*this, "LeanSTAmount.checked MPT", kCheckedMpt, checked(kIntegral));
        runRows(*this, "LeanSTAmount.checked IOU", kCheckedIou, checked(kFractional));
        runRows(
            *this, "LeanSTAmount.checked IOU, by mode", kCheckedIouByMode, checked(kFractional));
        runRows(*this, "LeanSTAmount.ofNumber XRP", kOfNumberXrp, ofNumber(kNative));
        runRows(*this, "LeanSTAmount.ofNumber MPT", kOfNumberMpt, ofNumber(kIntegral));
        runRows(*this, "LeanSTAmount.ofNumber IOU", kOfNumberIou, ofNumber(kFractional));
        runRows(*this, "LeanSTAmount.roundToScale", kRoundToScale, rounded);
        // Every sum is exact, so one mode covers them.
        runRows(*this, "LeanSTAmount.add overflow", kAddOverflow, add, kToNearestOnly);
        runRows(*this, "LeanSTAmount.sub underflow", kSubUnderflow, sub, kToNearestOnly);
    }

private:
    // Each list runs its rows under every rounding mode on the large mantissa scale (the IOU sums
    // under ToNearest only); a row that names a mode runs under that mode only, as its result
    // depends on the mode. A group comment names the row on the cusp; its rows move two values
    // around it. An IOU keeps 16 digits (10^15 to 10^16 - 1) at exponents -96 to 80.
    // - kCheckedXrp: the checked constructor takes XRP up to 10^17 drops and throws above
    //   (tecPATH_DRY); zero is tecPRECISION_LOSS.
    // - kCheckedMpt: MPT up to int64 max, above it throws (tecPATH_DRY). The commented rows break
    //   that rule: 2^63 and 2^63 + 1 at exponent 0 are accepted on both sides and stored as
    //   9'223'372'036'854'775'800.
    // - kCheckedIou: past 16 digits at exponent 80 throws (tecPATH_DRY), below them at -96 is zero
    //   (tecPRECISION_LOSS); 17 digits at 79 round into exponent 80 or past it as the mode rounds
    //   them (kCheckedIouByMode).
    // - kOfNumberXrp, kOfNumberMpt: a Number (m * 10^e as ToNearest stores it) to XRP up to 10^17
    //   drops and to MPT up to int64 max; above throws (tecPATH_DRY).
    // - kOfNumberIou: a Number to IOU. 10^16 - 1/2 at exponent 80 rounds into an overflow
    //   (tecPATH_DRY) under ToNearest and away from zero; the smallest IOU at -96, one ULP less
    //   rounds to zero (tecPRECISION_LOSS) or back up into range. The commented rows break the
    //   directed modes: for a negative amount both sides round the magnitude, so Downward rounds
    //   towards zero and Upward away from it.
    // - kRoundToScale: an IOU below `scale` rounds at 10^scale as the mode picks, ToNearest half to
    //   even; from `scale` up it is returned as is. The rows hold the amount C++ returns.
    // - kAddOverflow: add at exponent 80. A sum up to 10^16 - 1 fits, one more throws
    //   (tecPATH_DRY).
    // - kSubUnderflow: sub at exponent -96. a - b down to 10^15 is a value, one less is zero
    //   (tecPRECISION_LOSS).
    // clang-format off
    static constexpr CheckedCase kCheckedXrp[] = {
        // 100'000'000'000'000'000e0
        {.negative = false, .mantissa = 99'999'999'999'999'998, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'998, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'998, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'998, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'998, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'999, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'999, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'999, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'999, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'999, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'000, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 100'000'000'000'000'000, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 100'000'000'000'000'000, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 100'000'000'000'000'000, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'000, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'001, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 100'000'000'000'000'001, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 100'000'000'000'000'001, .exponent = 0, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'001, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'001, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'002, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 100'000'000'000'000'002, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 100'000'000'000'000'002, .exponent = 0, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'002, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 100'000'000'000'000'002, .exponent = 2, .expected = tecPATH_DRY},
        // 10'000'000'000'000'000e1
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'002, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'002, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'002, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'002, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'002, .exponent = 3, .expected = tecPATH_DRY},
        // 1e17
        {.negative = false, .mantissa = 0, .exponent = 15, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = 16, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = 17, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = 18, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = 19, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1, .exponent = 15, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1, .exponent = 17, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1, .exponent = 18, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 1, .exponent = 19, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 2, .exponent = 15, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 2, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 2, .exponent = 17, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 2, .exponent = 18, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 2, .exponent = 19, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 3, .exponent = 15, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 3, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 3, .exponent = 17, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 3, .exponent = 18, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 3, .exponent = 19, .expected = tecPATH_DRY},
        // -100'000'000'000'000'000e0
        {.negative = true, .mantissa = 100'000'000'000'000'002, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 100'000'000'000'000'002, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 100'000'000'000'000'002, .exponent = 0, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 100'000'000'000'000'002, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 100'000'000'000'000'002, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 100'000'000'000'000'001, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 100'000'000'000'000'001, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 100'000'000'000'000'001, .exponent = 0, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 100'000'000'000'000'001, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 100'000'000'000'000'001, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 100'000'000'000'000'000, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 100'000'000'000'000'000, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 100'000'000'000'000'000, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 100'000'000'000'000'000, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 100'000'000'000'000'000, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'999, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'999, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'999, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'999, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'999, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'998, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'998, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'998, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'998, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'998, .exponent = 2, .expected = tecPATH_DRY},
    };
    static constexpr CheckedCase kCheckedMpt[] = {
        // 9'223'372'036'854'775'807e0
        {.negative = false, .mantissa = 9'223'372'036'854'775'805, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'805, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'805, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'805, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'805, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'806, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'806, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'806, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'806, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'806, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'807, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'807, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'807, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'807, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'807, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = -1, .expected = tesSUCCESS},
        // {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = -2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = -1, .expected = tesSUCCESS},
        // {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 2, .expected = tecPATH_DRY},
        // -9'223'372'036'854'775'807e0
        {.negative = true, .mantissa = 9'223'372'036'854'775'805, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'805, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'805, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'805, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'805, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'806, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'806, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'806, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'806, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'806, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'807, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'807, .exponent = -1, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'807, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'807, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'807, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = -1, .expected = tesSUCCESS},
        // {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = -2, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = -1, .expected = tesSUCCESS},
        // {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 0, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 2, .expected = tecPATH_DRY},
        // 922'337'203'685'477'580e1
        {.negative = false, .mantissa = 922'337'203'685'477'578, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'578, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'578, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'578, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'578, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'579, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'579, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'579, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'579, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'579, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'580, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'580, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'580, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'580, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'580, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'581, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'581, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'581, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'581, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'581, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'582, .exponent = -1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'582, .exponent = 0, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 922'337'203'685'477'582, .exponent = 1, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'582, .exponent = 2, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 922'337'203'685'477'582, .exponent = 3, .expected = tecPATH_DRY},
        // 9'223'372'036'854'775e3
        {.negative = false, .mantissa = 9'223'372'036'854'773, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'773, .exponent = 2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'773, .exponent = 3, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'773, .exponent = 4, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'773, .exponent = 5, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'774, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'774, .exponent = 2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'774, .exponent = 3, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'774, .exponent = 4, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'774, .exponent = 5, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775, .exponent = 2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775, .exponent = 3, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775, .exponent = 4, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775, .exponent = 5, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'776, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'776, .exponent = 2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'776, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'776, .exponent = 4, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'776, .exponent = 5, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'777, .exponent = 1, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'777, .exponent = 2, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'777, .exponent = 3, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'777, .exponent = 4, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'777, .exponent = 5, .expected = tecPATH_DRY},
        // 9e18
        {.negative = false, .mantissa = 7, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 7, .exponent = 17, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 7, .exponent = 18, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 7, .exponent = 19, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 7, .exponent = 20, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 8, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 8, .exponent = 17, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 8, .exponent = 18, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 8, .exponent = 19, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 8, .exponent = 20, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9, .exponent = 17, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9, .exponent = 18, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9, .exponent = 19, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9, .exponent = 20, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10, .exponent = 17, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10, .exponent = 18, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10, .exponent = 19, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10, .exponent = 20, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 11, .exponent = 16, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 11, .exponent = 17, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 11, .exponent = 18, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 11, .exponent = 19, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 11, .exponent = 20, .expected = tecPATH_DRY},
    };
    static constexpr CheckedCase kCheckedIou[] = {
        // 9'999'999'999'999'999e80
        {.negative = false, .mantissa = 9'999'999'999'999'997, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'997, .exponent = 79, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'997, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'997, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 79, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'998, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 79, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 79, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 79, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'001, .exponent = 82, .expected = tecPATH_DRY},
        // 1'000'000'000'000'000e-96
        {.negative = false, .mantissa = 999'999'999'999'998, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'998, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'998, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'998, .exponent = -95, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 999'999'999'999'998, .exponent = -94, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 999'999'999'999'999, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999, .exponent = -95, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 999'999'999'999'999, .exponent = -94, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000, .exponent = -95, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000, .exponent = -94, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'001, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'001, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'001, .exponent = -96, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'001, .exponent = -95, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'001, .exponent = -94, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'002, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'002, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'002, .exponent = -96, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'002, .exponent = -95, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'002, .exponent = -94, .expected = tesSUCCESS},
        // 99'999'999'999'999'994e79
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 77, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 77, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 77, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 77, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 77, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 78, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 81, .expected = tecPATH_DRY},
        // -9'999'999'999'999'999e80
        {.negative = true, .mantissa = 10'000'000'000'000'001, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 10'000'000'000'000'001, .exponent = 79, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 10'000'000'000'000'001, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 10'000'000'000'000'001, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 10'000'000'000'000'001, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 10'000'000'000'000'000, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 10'000'000'000'000'000, .exponent = 79, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 10'000'000'000'000'000, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 10'000'000'000'000'000, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 10'000'000'000'000'000, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'999'999'999'999'999, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'999, .exponent = 79, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'999, .exponent = 80, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'999, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'999'999'999'999'999, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'999'999'999'999'998, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'998, .exponent = 79, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'998, .exponent = 80, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'998, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'999'999'999'999'998, .exponent = 82, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'999'999'999'999'997, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'997, .exponent = 79, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'997, .exponent = 80, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'999'999'999'999'997, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'999'999'999'999'997, .exponent = 82, .expected = tecPATH_DRY},
        // -1'000'000'000'000'000e-96
        {.negative = true, .mantissa = 1'000'000'000'000'002, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'002, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'002, .exponent = -96, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'002, .exponent = -95, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'002, .exponent = -94, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'001, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'001, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'001, .exponent = -96, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'001, .exponent = -95, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'001, .exponent = -94, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000, .exponent = -96, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000, .exponent = -95, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000, .exponent = -94, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 999'999'999'999'999, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999, .exponent = -95, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 999'999'999'999'999, .exponent = -94, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 999'999'999'999'998, .exponent = -98, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'998, .exponent = -97, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'998, .exponent = -96, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'998, .exponent = -95, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 999'999'999'999'998, .exponent = -94, .expected = tesSUCCESS},
        // -99'999'999'999'999'994e79
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 77, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 77, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 77, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 77, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 81, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 77, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 78, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 80, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 81, .expected = tecPATH_DRY},
    };
    static constexpr CheckedCase kCheckedIouByMode[] = {
        // 99'999'999'999'999'994e79
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.negative = false, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.negative = false, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.negative = false, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.negative = false, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.negative = false, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        // -99'999'999'999'999'994e79
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.negative = true, .mantissa = 99'999'999'999'999'996, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.negative = true, .mantissa = 99'999'999'999'999'995, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.negative = true, .mantissa = 99'999'999'999'999'994, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.negative = true, .mantissa = 99'999'999'999'999'993, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Downward},
        {.negative = true, .mantissa = 99'999'999'999'999'992, .exponent = 79, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
    };
    static constexpr OfNumberCase kOfNumberXrp[] = {
        // 100'000'000'000'000'000e0
        {.mantissa = 99'999'999'999'999'998, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'998, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'998, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'998, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'998, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'999, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'999, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'999, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 99'999'999'999'999'999, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 99'999'999'999'999'999, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'000, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 100'000'000'000'000'000, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 100'000'000'000'000'000, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 100'000'000'000'000'000, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'000, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'001, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 100'000'000'000'000'001, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 100'000'000'000'000'001, .exponent = 0, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'001, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'001, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'002, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = 100'000'000'000'000'002, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 100'000'000'000'000'002, .exponent = 0, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'002, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 100'000'000'000'000'002, .exponent = 2, .expected = tecPATH_DRY},
        // 10'000'000'000'000'000e1
        {.mantissa = 9'999'999'999'999'998, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'998, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'998, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'998, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'998, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'999, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'999, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'999, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = 9'999'999'999'999'999, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 9'999'999'999'999'999, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'000, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'000, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'000, .exponent = 1, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'000, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'000, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'001, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'001, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'001, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'001, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'001, .exponent = 3, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'002, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'002, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = 10'000'000'000'000'002, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'002, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = 10'000'000'000'000'002, .exponent = 3, .expected = tecPATH_DRY},
        // 1e17
        {.mantissa = 0, .exponent = 15, .expected = tecPRECISION_LOSS},
        {.mantissa = 0, .exponent = 16, .expected = tecPRECISION_LOSS},
        {.mantissa = 0, .exponent = 17, .expected = tecPRECISION_LOSS},
        {.mantissa = 0, .exponent = 18, .expected = tecPRECISION_LOSS},
        {.mantissa = 0, .exponent = 19, .expected = tecPRECISION_LOSS},
        {.mantissa = 1, .exponent = 15, .expected = tesSUCCESS},
        {.mantissa = 1, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 1, .exponent = 17, .expected = tesSUCCESS},
        {.mantissa = 1, .exponent = 18, .expected = tecPATH_DRY},
        {.mantissa = 1, .exponent = 19, .expected = tecPATH_DRY},
        {.mantissa = 2, .exponent = 15, .expected = tesSUCCESS},
        {.mantissa = 2, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 2, .exponent = 17, .expected = tecPATH_DRY},
        {.mantissa = 2, .exponent = 18, .expected = tecPATH_DRY},
        {.mantissa = 2, .exponent = 19, .expected = tecPATH_DRY},
        {.mantissa = 3, .exponent = 15, .expected = tesSUCCESS},
        {.mantissa = 3, .exponent = 16, .expected = tesSUCCESS},
        {.mantissa = 3, .exponent = 17, .expected = tecPATH_DRY},
        {.mantissa = 3, .exponent = 18, .expected = tecPATH_DRY},
        {.mantissa = 3, .exponent = 19, .expected = tecPATH_DRY},
        // -100'000'000'000'000'000e0
        {.mantissa = -100'000'000'000'000'002, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -100'000'000'000'000'002, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -100'000'000'000'000'002, .exponent = 0, .expected = tecPATH_DRY},
        {.mantissa = -100'000'000'000'000'002, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -100'000'000'000'000'002, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -100'000'000'000'000'001, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -100'000'000'000'000'001, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -100'000'000'000'000'001, .exponent = 0, .expected = tecPATH_DRY},
        {.mantissa = -100'000'000'000'000'001, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -100'000'000'000'000'001, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -100'000'000'000'000'000, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -100'000'000'000'000'000, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -100'000'000'000'000'000, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -100'000'000'000'000'000, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -100'000'000'000'000'000, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'999, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'999, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'999, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'999, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'999, .exponent = 2, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'998, .exponent = -2, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'998, .exponent = -1, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'998, .exponent = 0, .expected = tesSUCCESS},
        {.mantissa = -99'999'999'999'999'998, .exponent = 1, .expected = tecPATH_DRY},
        {.mantissa = -99'999'999'999'999'998, .exponent = 2, .expected = tecPATH_DRY},
    };
    static constexpr OfNumberCase kOfNumberMpt[] = {
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
    static constexpr OfNumberCase kOfNumberIou[] = {
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
        // {.mantissa = -999'999'999'999'999'952, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        // {.mantissa = -999'999'999'999'999'952, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'952, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'952, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'951, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'951, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        // {.mantissa = -999'999'999'999'999'951, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'951, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'951, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'950, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'950, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        // {.mantissa = -999'999'999'999'999'950, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'950, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'950, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'949, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'949, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        // {.mantissa = -999'999'999'999'999'949, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'949, .exponent = 79, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'949, .exponent = 80, .expected = tecPATH_DRY},
        {.mantissa = -999'999'999'999'999'948, .exponent = 76, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'948, .exponent = 77, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        // {.mantissa = -999'999'999'999'999'948, .exponent = 78, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
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
        // {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        // {.mantissa = -999'999'999'999'999'999, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'999, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'999, .exponent = -97, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -101, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -100, .expected = tecPRECISION_LOSS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        // {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        // {.mantissa = -999'999'999'999'999'998, .exponent = -99, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.mantissa = -999'999'999'999'999'998, .exponent = -98, .expected = tesSUCCESS},
        {.mantissa = -999'999'999'999'999'998, .exponent = -97, .expected = tesSUCCESS},
    };
    static constexpr RoundToScaleCase kRoundToScale[] = {
        // 1'000'000'000'000'005e-1 to scale 0
        {.mantissa = 1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        // 1'000'000'000'000'015e-1 to scale 0
        {.mantissa = 1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        // -1'000'000'000'000'005e-1 to scale 0
        {.mantissa = -1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'007, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'006, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'004, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'003, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        // -1'000'000'000'000'015e-1 to scale 0
        {.mantissa = -1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'017, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'016, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'015, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'014, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'020, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'013, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        // 9'999'999'999'999'995e-11 to scale -10
        {.mantissa = 9'999'999'999'999'993, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'999'999'999'999'993, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'999'999'999'999'993, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'999'999'999'999'993, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'999'999'999'999'994, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'999'999'999'999'994, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'999'999'999'999'994, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'999'999'999'999'994, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'999'999'999'999'995, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'999'999'999'999'995, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'999'999'999'999'995, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'999'999'999'999'995, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'999'999'999'999'996, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'999'999'999'999'996, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'999'999'999'999'996, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'999'999'999'999'996, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'999'999'999'999'997, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'999'999'999'999'997, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'999'999'999'999'997, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'999'999'999'999'997, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::Upward},
        // 1'000'000'000'000'005e0 to scale 0
        {.mantissa = 1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -2}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -2}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -2}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'100, .exponent = -2}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'005, .exponent = 0, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'005, .exponent = 0}},
        {.mantissa = 1'000'000'000'000'005, .exponent = 1, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'005, .exponent = 1}},
        {.mantissa = 1'000'000'000'000'005, .exponent = 2, .scale = 0, .expected = {.mantissa = 1'000'000'000'000'005, .exponent = 2}},
        // -1'000'000'000'000'005e0 to scale 0
        {.mantissa = -1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -2}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -2}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'100, .exponent = -2}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'005, .exponent = -2, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -2}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'010, .exponent = -1}, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'005, .exponent = -1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'000, .exponent = -1}, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'005, .exponent = 0, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'005, .exponent = 0}},
        {.mantissa = -1'000'000'000'000'005, .exponent = 1, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'005, .exponent = 1}},
        {.mantissa = -1'000'000'000'000'005, .exponent = 2, .scale = 0, .expected = {.mantissa = -1'000'000'000'000'005, .exponent = 2}},
        // 9'999'999'999'999'999e-10 to scale -10
        {.mantissa = 9'999'999'999'999'999, .exponent = -12, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -11}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'999'999'999'999'999, .exponent = -12, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'900, .exponent = -12}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'999'999'999'999'999, .exponent = -12, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'900, .exponent = -12}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'999'999'999'999'999, .exponent = -12, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -11}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'999'999'999'999'999, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'999'999'999'999'999, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'999'999'999'999'999, .exponent = -11, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'990, .exponent = -11}, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'999'999'999'999'999, .exponent = -11, .scale = -10, .expected = {.mantissa = 1'000'000'000'000'000, .exponent = -10}, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'999'999'999'999'999, .exponent = -10, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -10}},
        {.mantissa = 9'999'999'999'999'999, .exponent = -9, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -9}},
        {.mantissa = 9'999'999'999'999'999, .exponent = -8, .scale = -10, .expected = {.mantissa = 9'999'999'999'999'999, .exponent = -8}},
    };
    static constexpr PairCase kAddOverflow[] = {
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
    static constexpr PairCase kSubUnderflow[] = {
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
        // The Lean model assumes all amendments.
        std::unordered_set<uint256, beast::Uhash<>> const amendments{
            featureMPTokensV2, featureSingleAssetVault, featureLendingProtocol};
        CurrentTransactionRulesGuard const rules{Rules{amendments}};

        test_fuzz_round_to_exponent();
        test_fuzz_compare();
        test_fuzz_neg();
        test_fuzz_unchecked_from_int64();
        test_fuzz_add_sub();
        test_fuzz_accessors();
        test_fuzz_constructors();
        test_known_construction();
        test_known_comparison();
        test_known_arithmetic();
        test_known_round_to_exponent();
        test_extreme_values();
        test_integral_int64_wrap();
        testBoundaries();

        // Known discrepancies, each fails until the C++ code is fixed.
        // clang-format off
        // test_add_xrp_overflow();          // FV_M2_1: XRP operator+ at INT64_MAX wraps negative
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanSTAmount, formal_verification, xrpl);

}  // namespace xrpl::test
