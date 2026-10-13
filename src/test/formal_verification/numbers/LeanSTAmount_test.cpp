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
#include <xrpl/protocol/IOUAmount.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/MPTAmount.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/STAmount.h>

#include <cstdint>
#include <exception>
#include <initializer_list>
#include <limits>
#include <sstream>
#include <string>
#include <tuple>

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
lean_stamount_of_int64(lean_object*, int64_t, int64_t, uint8_t);
lean_object*
lean_stamount_of_number(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_lt(lean_object*, lean_object*);
lean_object*
lean_stamount_add(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_sub(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_multiply(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_divide(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_mul_round(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object*
lean_stamount_mul_round_strict(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object*
lean_stamount_div_round(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object*
lean_stamount_div_round_strict(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object*
lean_stamount_can_add(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_can_subtract(lean_object*, lean_object*);
lean_object*
lean_stamount_round_to_exponent(lean_object*, int64_t, uint8_t);
uint64_t
lean_stamount_get_rate(lean_object*, lean_object*, uint8_t);
lean_object*
lean_stamount_neg(lean_object*);
lean_object*
lean_stamount_unchecked_from_int64(lean_object*, int64_t, int64_t);
uint8_t
lean_stamount_eq(lean_object*, lean_object*);
uint8_t
lean_stamount_ne(lean_object*, lean_object*);
lean_object*
lean_stamount_le(lean_object*, lean_object*);
lean_object*
lean_stamount_gt(lean_object*, lean_object*);
lean_object*
lean_stamount_ge(lean_object*, lean_object*);
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

    bool
    checkStAmountResult(
        std::string const& tag,
        LeanSTAmountResult const& lean,
        STAmount const& cpp,
        bool cppThrew)
    {
        if (lean.ok == cppThrew)
        {
            std::stringstream ss;
            ss << tag << ": error mismatch lean.ok=" << lean.ok << " cppThrew=" << cppThrew;
            fail(ss.str());
            return false;
        }
        if (!lean.ok)
        {
            pass();
            return true;
        }
        if (!stAmountFieldsEqual(lean, cpp))
        {
            std::stringstream ss;
            ss << tag << ": value mismatch lean=" << format(lean) << " cpp=" << format(cpp);
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    template <typename CppFn>
    bool
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

    bool
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

    bool
    checkOfInt64(uint8_t nt, int64_t mantissa, int64_t exponent, Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        std::stringstream tag;
        tag << "ofInt64(nt=" << static_cast<int>(nt) << "," << mantissa << "e" << exponent << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                lean_stamount_of_int64,
                NumericTypeFFI::build(nt),
                mantissa,
                exponent,
                toLeanMode(mode))),
            [&] {
                return assetForNumericType(nt).visit(
                    [&](Issue const& iss) {
                        return STAmount{iss, mantissa, static_cast<int>(exponent)};
                    },
                    [&](MPTIssue const& mpt) {
                        return STAmount{mpt, mantissa, static_cast<int>(exponent)};
                    });
            });
    }

    bool
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
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                leanFn,
                STAmountFFI::build(
                    a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
                STAmountFFI::build(
                    b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative),
                toLeanMode(mode))),
            [&] { return isAdd ? (a.cppSt + b.cppSt) : (a.cppSt - b.cppSt); });
    }

    bool
    checkMultiply(
        STAmountPair const& a,
        STAmountPair const& b,
        uint8_t nt,
        Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        std::stringstream tag;
        tag << "multiply(nt1=" << static_cast<int>(a.leanSt.numericType)
            << ",nt2=" << static_cast<int>(b.leanSt.numericType) << ",nt=" << static_cast<int>(nt)
            << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                lean_stamount_multiply,
                STAmountFFI::build(
                    a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
                STAmountFFI::build(
                    b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative),
                NumericTypeFFI::build(nt),
                toLeanMode(mode))),
            [&] { return multiply(a.cppSt, b.cppSt, assetForNumericType(nt)); });
    }

    bool
    checkDivide(
        STAmountPair const& num,
        STAmountPair const& den,
        uint8_t nt,
        Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        std::stringstream tag;
        tag << "divide(ntN=" << static_cast<int>(num.leanSt.numericType)
            << ",ntD=" << static_cast<int>(den.leanSt.numericType) << ",nt=" << static_cast<int>(nt)
            << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                lean_stamount_divide,
                STAmountFFI::build(
                    num.leanSt.numericType,
                    num.leanSt.mValue,
                    num.leanSt.mOffset,
                    num.leanSt.isNegative),
                STAmountFFI::build(
                    den.leanSt.numericType,
                    den.leanSt.mValue,
                    den.leanSt.mOffset,
                    den.leanSt.isNegative),
                NumericTypeFFI::build(nt),
                toLeanMode(mode))),
            [&] { return divide(num.cppSt, den.cppSt, assetForNumericType(nt)); });
    }

    template <typename LeanFn, typename CppFn>
    bool
    checkMulRoundLike(
        char const* op,
        LeanFn leanFn,
        CppFn cppFn,
        STAmountPair const& a,
        STAmountPair const& b,
        uint8_t nt,
        bool roundUp,
        Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        std::stringstream tag;
        tag << op << "(nt1=" << static_cast<int>(a.leanSt.numericType)
            << ",nt2=" << static_cast<int>(b.leanSt.numericType) << ",nt=" << static_cast<int>(nt)
            << ",ru=" << roundUp << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                leanFn,
                STAmountFFI::build(
                    a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
                STAmountFFI::build(
                    b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative),
                NumericTypeFFI::build(nt),
                roundUp ? 1u : 0u,
                toLeanMode(mode))),
            [&] { return cppFn(a.cppSt, b.cppSt, assetForNumericType(nt), roundUp); });
    }

    template <typename LeanFn, typename CppFn>
    bool
    checkDivRoundLike(
        char const* op,
        LeanFn leanFn,
        CppFn cppFn,
        STAmountPair const& num,
        STAmountPair const& den,
        uint8_t nt,
        bool roundUp,
        Number::RoundingMode mode)
    {
        NumberRoundModeGuard mg(mode);
        std::stringstream tag;
        tag << op << "(ntN=" << static_cast<int>(num.leanSt.numericType)
            << ",ntD=" << static_cast<int>(den.leanSt.numericType) << ",nt=" << static_cast<int>(nt)
            << ",ru=" << roundUp << ")";
        return runSTAmountOp(
            tag.str(),
            STAmountFFI::fromExcept(leanCall(
                leanFn,
                STAmountFFI::build(
                    num.leanSt.numericType,
                    num.leanSt.mValue,
                    num.leanSt.mOffset,
                    num.leanSt.isNegative),
                STAmountFFI::build(
                    den.leanSt.numericType,
                    den.leanSt.mValue,
                    den.leanSt.mOffset,
                    den.leanSt.isNegative),
                NumericTypeFFI::build(nt),
                roundUp ? 1u : 0u,
                toLeanMode(mode))),
            [&] { return cppFn(num.cppSt, den.cppSt, assetForNumericType(nt), roundUp); });
    }

    bool
    checkCanAdd(STAmountPair const& a, STAmountPair const& b, Number::RoundingMode mode)
    {
        uint8_t const leanMode = toLeanMode(mode);
        NumberRoundModeGuard mg(mode);
        auto lean = readExcept<BoolFFI>(leanCall(
            lean_stamount_can_add,
            STAmountFFI::build(
                a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
            STAmountFFI::build(
                b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative),
            leanMode));
        bool cppThrew = false;
        bool cppRet = false;
        try
        {
            cppRet = canAdd(a.cppSt, b.cppSt);
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        std::stringstream tag;
        tag << "canAdd(nt1=" << static_cast<int>(a.leanSt.numericType)
            << ",nt2=" << static_cast<int>(b.leanSt.numericType) << ")";
        if (lean.value.has_value() == cppThrew)
        {
            fail(tag.str() + ": error mismatch");
            return false;
        }
        if (lean.value.has_value() && lean.value->read() != cppRet)
        {
            std::stringstream ss;
            ss << tag.str() << ": value mismatch lean=" << lean.value->read() << " cpp=" << cppRet;
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    bool
    checkCanSub(STAmountPair const& a, STAmountPair const& b)
    {
        auto lean = readExcept<BoolFFI>(leanCall(
            lean_stamount_can_subtract,
            STAmountFFI::build(
                a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
            STAmountFFI::build(
                b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative)));
        bool cppThrew = false;
        bool cppRet = false;
        try
        {
            cppRet = canSubtract(a.cppSt, b.cppSt);
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        std::stringstream tag;
        tag << "canSub(nt1=" << static_cast<int>(a.leanSt.numericType)
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
    checkGetRate(
        STAmountPair const& offerOut,
        STAmountPair const& offerIn,
        Number::RoundingMode mode)
    {
        uint8_t const leanMode = toLeanMode(mode);
        NumberRoundModeGuard mg(mode);
        uint64_t const lean = leanCall(
            lean_stamount_get_rate,
            STAmountFFI::build(
                offerOut.leanSt.numericType,
                offerOut.leanSt.mValue,
                offerOut.leanSt.mOffset,
                offerOut.leanSt.isNegative),
            STAmountFFI::build(
                offerIn.leanSt.numericType,
                offerIn.leanSt.mValue,
                offerIn.leanSt.mOffset,
                offerIn.leanSt.isNegative),
            leanMode);
        uint64_t const cpp = getRate(offerOut.cppSt, offerIn.cppSt);
        if (lean != cpp)
        {
            std::stringstream ss;
            ss << "getRate(ntOut=" << static_cast<int>(offerOut.leanSt.numericType)
               << ",ntIn=" << static_cast<int>(offerIn.leanSt.numericType) << "): lean=" << lean
               << " cpp=" << cpp;
            fail(ss.str());
            return false;
        }
        pass();
        return true;
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
    checkNe(STAmountPair const& a, STAmountPair const& b)
    {
        return expectBool(
            "ne",
            leanCall(
                lean_stamount_ne,
                STAmountFFI::build(
                    a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
                STAmountFFI::build(
                    b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative)),
            a.cppSt != b.cppSt);
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
    checkGe(STAmountPair const& a, STAmountPair const& b)
    {
        bool cpp = false, cppThrew = false;
        try
        {
            cpp = a.cppSt >= b.cppSt;
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }
        return checkOrdering("ge", lean_stamount_ge, cpp, cppThrew, a, b);
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

    bool
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

    bool
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

        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
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

        checkOfInt64(kIntegral, 1'000'000, 0, m);
        checkOfInt64(kIntegral, -1'000'000, 0, m);
        checkOfInt64(kNative, 1'000'000, 0, m);
        checkOfInt64(kNative, -1'000'000, 0, m);
        checkOfInt64(kIntegral, 999'999'999LL, 0, m);
        checkOfInt64(kIntegral, -999'999'999LL, 0, m);
        checkOfInt64(kFractional, 1'234'567'890LL, 0, m);
        checkOfInt64(kFractional, -1'234'567'890LL, 0, m);

        for (auto nt : {kIntegral, kFractional})
        {
            for (auto [neg, mant, exp_] :
                 std::initializer_list<std::tuple<uint8_t, uint64_t, int64_t>>{
                     {0, 0, 0},
                     {0, 1'000'000'000'000'000'000ULL, 0},
                     {1, 1'000'000'000'000'000'000ULL, 0},
                     {0, 1'234'567'890'123'456'789ULL, -2}})
            {
                NumberRoundModeGuard mg(m);
                uint8_t const leanMode = toLeanMode(m);
                auto lean = STAmountFFI::fromExcept(leanCall(
                    lean_stamount_of_number,
                    NumericTypeFFI::build(nt),
                    lean_number_build(neg, mant, exp_),
                    leanMode));
                STAmount cpp;
                bool cppThrew = false;
                try
                {
                    Number const n{neg != 0, mant, static_cast<int>(exp_), Number::Unchecked{}};
                    cpp = assetForNumericType(nt).visit(
                        [&](Issue const& iss) { return STAmount{iss, n}; },
                        [&](MPTIssue const& mpt) { return STAmount{mpt, n}; });
                }
                catch (std::exception const&)
                {
                    cppThrew = true;
                }
                std::stringstream tag;
                tag << "ofNumber(nt=" << static_cast<int>(nt) << "," << (neg ? "-" : "+") << mant
                    << "e" << exp_ << ")";
                checkStAmountResult(tag.str(), lean, cpp, cppThrew);
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
            makeSTAmountPair(kIntegral, 1'000, 0, 0),
            makeSTAmountPair(kIntegral, 2'000, 0, 0),
            m);
        checkAddSub(
            "sub",
            false,
            makeSTAmountPair(kIntegral, 5'000, 0, 0),
            makeSTAmountPair(kIntegral, 2'000, 0, 0),
            m);
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kIntegral, 0, 0, 0),
            makeSTAmountPair(kIntegral, 2'000, 0, 0),
            m);
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kIntegral, 5'000, 0, 0),
            makeSTAmountPair(kIntegral, 0, 0, 0),
            m);
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

        // Mode sweep on a non-trivial IOU sum.
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            checkAddSub(
                "add",
                true,
                makeSTAmountPair(kFractional, 1'234'567'890'123'456ULL, 0, 0),
                makeSTAmountPair(kFractional, 9'876'543'210'987'654ULL, -3, 1),
                mode);
        }

        checkMultiply(
            makeSTAmountPair(kIntegral, 1'000, 0, 0),
            makeSTAmountPair(kIntegral, 1'000, 0, 0),
            kIntegral,
            m);
        checkMultiply(
            makeSTAmountPair(kFractional, 2'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
            kFractional,
            m);
        // IOU × IOU result rounded into an integral (MPT) target — the ofNumber integral path.
        checkMultiply(
            makeSTAmountPair(kFractional, 2'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
            kIntegral,
            m);
        checkMultiply(
            makeSTAmountPair(kIntegral, 0, 0, 0),
            makeSTAmountPair(kIntegral, 1'000, 0, 0),
            kIntegral,
            m);
        checkMultiply(
            makeSTAmountPair(kFractional, 0, -100, 0),
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            kFractional,
            m);

        checkDivide(
            makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
            kFractional,
            m);
        // den = 0 errors on both sides; num = 0 short-circuits to zero.
        checkDivide(
            makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 0, -100, 0),
            kFractional,
            m);
        checkDivide(
            makeSTAmountPair(kFractional, 0, -100, 0),
            makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
            kFractional,
            m);
        // 1 / 1 (integral) into a fractional target — the kURateOne recipe.
        checkDivide(
            makeSTAmountPair(kIntegral, 1, 0, 0),
            makeSTAmountPair(kIntegral, 1, 0, 0),
            kFractional,
            m);
        checkDivide(
            makeSTAmountPair(kIntegral, 100, 0, 0),
            makeSTAmountPair(kIntegral, 200, 0, 0),
            kFractional,
            m);

        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            checkDivide(
                makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
                makeSTAmountPair(kFractional, 7'000'000'000'000'000ULL, 0, 0),
                kFractional,
                mode);
        }
    }

    void
    test_known_rounding()
    {
        beginCase("LeanSTAmount.known_rounding");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;

        auto const mulRoundFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &mulRound);
        auto const mulRoundStrictFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &mulRoundStrict);

        // mulRound and mulRoundStrict, both roundUp values, across numericTypes.
        for (bool ru : {false, true})
        {
            checkMulRoundLike(
                "mulRound",
                lean_stamount_mul_round,
                mulRoundFn,
                makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
                makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
                kFractional,
                ru,
                m);
            checkMulRoundLike(
                "mulRoundStrict",
                lean_stamount_mul_round_strict,
                mulRoundStrictFn,
                makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
                makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
                kFractional,
                ru,
                m);
            // Tiny non-negative input: roundUp=true rescues to smallest-above-zero.
            checkMulRoundLike(
                "mulRound",
                lean_stamount_mul_round,
                mulRoundFn,
                makeSTAmountPair(kFractional, STAmount::kMinValue, STAmount::kMinOffset, 0),
                makeSTAmountPair(kFractional, STAmount::kMinValue, STAmount::kMinOffset, 0),
                kFractional,
                ru,
                m);
            // integral × integral → integral fast path.
            checkMulRoundLike(
                "mulRound",
                lean_stamount_mul_round,
                mulRoundFn,
                makeSTAmountPair(kIntegral, 1'000, 0, 0),
                makeSTAmountPair(kIntegral, 1'000, 0, 0),
                kIntegral,
                ru,
                m);
            checkMulRoundLike(
                "mulRoundStrict",
                lean_stamount_mul_round_strict,
                mulRoundStrictFn,
                makeSTAmountPair(kIntegral, 1'000, 0, 0),
                makeSTAmountPair(kIntegral, 1'000, 0, 0),
                kIntegral,
                ru,
                m);
            // Zero short-circuit.
            checkMulRoundLike(
                "mulRound",
                lean_stamount_mul_round,
                mulRoundFn,
                makeSTAmountPair(kFractional, 0, -100, 0),
                makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
                kFractional,
                ru,
                m);
        }

        // canonicalizeRound's `resultNegative != roundUp` branch.
        checkMulRoundLike(
            "mulRound",
            lean_stamount_mul_round,
            mulRoundFn,
            makeSTAmountPair(kFractional, 1'234'567'890'123'456ULL, 0, 0),
            makeSTAmountPair(kFractional, 9'876'543'210'987'654ULL, 0, 1),
            kFractional,
            true,
            m);

        auto const divRoundFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &divRound);
        auto const divRoundStrictFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &divRoundStrict);

        for (bool ru : {false, true})
        {
            checkDivRoundLike(
                "divRound",
                lean_stamount_div_round,
                divRoundFn,
                makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
                makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
                kFractional,
                ru,
                m);
            checkDivRoundLike(
                "divRoundStrict",
                lean_stamount_div_round_strict,
                divRoundStrictFn,
                makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
                makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
                kFractional,
                ru,
                m);
            // Tiny positive numerator with large denominator: roundUp=true rescues.
            checkDivRoundLike(
                "divRound",
                lean_stamount_div_round,
                divRoundFn,
                makeSTAmountPair(kFractional, STAmount::kMinValue, STAmount::kMinOffset, 0),
                makeSTAmountPair(kFractional, STAmount::kMaxValue, STAmount::kMaxOffset, 0),
                kFractional,
                ru,
                m);
            // den = 0 errors on both sides; num = 0 short-circuits.
            checkDivRoundLike(
                "divRound",
                lean_stamount_div_round,
                divRoundFn,
                makeSTAmountPair(kFractional, 1'000'000'000'000'000ULL, 0, 0),
                makeSTAmountPair(kFractional, 0, -100, 0),
                kFractional,
                ru,
                m);
            checkDivRoundLike(
                "divRound",
                lean_stamount_div_round,
                divRoundFn,
                makeSTAmountPair(kFractional, 0, -100, 0),
                makeSTAmountPair(kFractional, 3'000'000'000'000'000ULL, 0, 0),
                kFractional,
                ru,
                m);
        }
    }

    void
    test_known_predicates()
    {
        beginCase("LeanSTAmount.known_predicates");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;

        constexpr uint64_t kMaxIntegral =
            static_cast<uint64_t>(std::numeric_limits<int64_t>::max());

        // canAdd at INT64_MAX ± 1 (overflow on both signs), zero short-circuit, happy path.
        checkCanAdd(
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0),
            makeSTAmountPair(kIntegral, 1, 0, 0),
            m);
        checkCanAdd(
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 1),
            makeSTAmountPair(kIntegral, 1, 0, 1),
            m);
        checkCanAdd(makeSTAmountPair(kIntegral, 0, 0, 0), makeSTAmountPair(kIntegral, 1, 0, 0), m);
        checkCanAdd(makeSTAmountPair(kIntegral, 1, 0, 0), makeSTAmountPair(kIntegral, 0, 0, 0), m);
        checkCanAdd(
            makeSTAmountPair(kIntegral, 1'000, 0, 0), makeSTAmountPair(kIntegral, 2'000, 0, 0), m);

        // IOU precision-loss path: equal magnitudes vs vastly different magnitudes.
        checkCanAdd(
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kFractional, 5'000'000'000'000'000ULL, 0, 0),
            m);
        checkCanAdd(
            makeSTAmountPair(kFractional, STAmount::kMaxValue, STAmount::kMaxOffset, 0),
            makeSTAmountPair(kFractional, STAmount::kMinValue, STAmount::kMinOffset, 0),
            m);

        // Cross-type canAdd → false on both sides.
        checkCanAdd(
            makeSTAmountPair(kIntegral, 100, 0, 0),
            makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0),
            m);

        // canSubtract: integral underflow, in-range, IOU always true, zero shortcut.
        checkCanSub(makeSTAmountPair(kIntegral, 100, 0, 0), makeSTAmountPair(kIntegral, 200, 0, 0));
        checkCanSub(
            makeSTAmountPair(kIntegral, 1'000, 0, 0), makeSTAmountPair(kIntegral, 100, 0, 0));
        checkCanSub(
            makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0),
            makeSTAmountPair(kFractional, STAmount::kMaxValue, STAmount::kMaxOffset, 0));
        checkCanSub(makeSTAmountPair(kIntegral, 0, 0, 0), makeSTAmountPair(kIntegral, 1'000, 0, 0));
        checkCanSub(
            makeSTAmountPair(kIntegral, 100, 0, 0),
            makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0));
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
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            checkRoundToExponent(
                makeSTAmountPair(kFractional, 1'234'567'890'123'456ULL, -10, 0), -5, mode);
            checkRoundToExponent(
                makeSTAmountPair(kFractional, 1'234'567'890'123'456ULL, -10, 1), -5, mode);
        }
    }

    void
    test_known_get_rate()
    {
        beginCase("LeanSTAmount.known_get_rate");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;

        // offerOut == 0 → 0.
        checkGetRate(
            makeSTAmountPair(kIntegral, 0, 0, 0), makeSTAmountPair(kIntegral, 100, 0, 0), m);
        // 1 / 1 — the kURateOne recipe.
        checkGetRate(makeSTAmountPair(kIntegral, 1, 0, 0), makeSTAmountPair(kIntegral, 1, 0, 0), m);
        checkGetRate(
            makeSTAmountPair(kIntegral, 1, 0, 0), makeSTAmountPair(kIntegral, 10, 0, 0), m);
        checkGetRate(
            makeSTAmountPair(kIntegral, 10, 0, 0), makeSTAmountPair(kIntegral, 1, 0, 0), m);
        checkGetRate(
            makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0),
            makeSTAmountPair(kFractional, STAmount::kMinValue, 1, 0),
            m);
        // Mixed-type: both sides go through divide(in, out, fractional).
        checkGetRate(
            makeSTAmountPair(kIntegral, 1, 0, 0),
            makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0),
            m);
        checkGetRate(
            makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0),
            makeSTAmountPair(kIntegral, 1, 0, 0),
            m);

        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            checkGetRate(
                makeSTAmountPair(kFractional, STAmount::kMinValue, 0, 0),
                makeSTAmountPair(kFractional, 7'000'000'000'000'000ULL, 0, 0),
                mode);
        }
    }

    void
    test_fuzz_accessors()
    {
        beginCase("LeanSTAmount.fuzz_accessors", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
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
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            // checked: hits canonicalization + boundary errors per numericType.
            runFuzz(10'000, [&] { return checkChecked(randomSTAmountPair(rng), mode); });
            // ofInt64: mantissa drawn as signed int64, numericType picked uniformly.
            std::uniform_int_distribution<int64_t> mDist(
                std::numeric_limits<int64_t>::min(), std::numeric_limits<int64_t>::max());
            std::uniform_int_distribution<int> eDist(-10, 10);
            runFuzz(10'000, [&] {
                uint8_t const nt = randomNumericType(rng);
                int64_t const mant = mDist(rng);
                int64_t const exp_ = eDist(rng);
                return checkOfInt64(nt, mant, exp_, mode);
            });
        }
    }

    void
    test_fuzz_add_sub()
    {
        beginCase("LeanSTAmount.fuzz_add_sub", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            std::bernoulli_distribution opDist(0.5);
            runFuzz(10'000, [&] {
                bool const isAdd = opDist(rng);
                auto a = randomSTAmountPair(rng);
                auto b = randomSTAmountPair(rng);
                return checkAddSub(isAdd ? "add" : "sub", isAdd, a, b, mode);
            });
        }
    }

    void
    test_fuzz_multiply_divide()
    {
        beginCase("LeanSTAmount.fuzz_multiply_divide", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(10'000, [&] {
                auto a = randomSTAmountPair(rng);
                auto b = randomSTAmountPair(rng);
                uint8_t const nt = randomNumericType(rng);
                return checkMultiply(a, b, nt, mode);
            });
            runFuzz(10'000, [&] {
                auto a = randomSTAmountPair(rng);
                auto b = randomSTAmountPair(rng);
                uint8_t const nt = randomNumericType(rng);
                return checkDivide(a, b, nt, mode);
            });
        }
    }

    void
    test_fuzz_mul_round()
    {
        beginCase("LeanSTAmount.fuzz_mul_round", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        std::bernoulli_distribution ruDist(0.5);
        std::bernoulli_distribution strictDist(0.5);
        auto const mulRoundFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &mulRound);
        auto const mulRoundStrictFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &mulRoundStrict);
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(10'000, [&] {
                auto a = randomSTAmountPair(rng);
                auto b = randomSTAmountPair(rng);
                bool const strict = strictDist(rng);
                uint8_t const nt = randomNumericType(rng);
                bool const ru = ruDist(rng);
                if (strict)
                    return checkMulRoundLike(
                        "mulRoundStrict",
                        lean_stamount_mul_round_strict,
                        mulRoundStrictFn,
                        a,
                        b,
                        nt,
                        ru,
                        mode);
                return checkMulRoundLike(
                    "mulRound", lean_stamount_mul_round, mulRoundFn, a, b, nt, ru, mode);
            });
        }
    }

    void
    test_fuzz_div_round()
    {
        beginCase("LeanSTAmount.fuzz_div_round", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        std::bernoulli_distribution ruDist(0.5);
        std::bernoulli_distribution strictDist(0.5);
        auto const divRoundFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &divRound);
        auto const divRoundStrictFn =
            static_cast<STAmount (*)(STAmount const&, STAmount const&, Asset const&, bool)>(
                &divRoundStrict);
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(10'000, [&] {
                auto num = randomSTAmountPair(rng);
                auto den = randomSTAmountPair(rng);
                bool const strict = strictDist(rng);
                uint8_t const nt = randomNumericType(rng);
                bool const ru = ruDist(rng);
                if (strict)
                    return checkDivRoundLike(
                        "divRoundStrict",
                        lean_stamount_div_round_strict,
                        divRoundStrictFn,
                        num,
                        den,
                        nt,
                        ru,
                        mode);
                return checkDivRoundLike(
                    "divRound", lean_stamount_div_round, divRoundFn, num, den, nt, ru, mode);
            });
        }
    }

    void
    test_fuzz_predicates()
    {
        beginCase("LeanSTAmount.fuzz_predicates", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(10'000, [&] {
                auto a = randomSTAmountPair(rng);
                auto b = randomSTAmountPair(rng);
                return checkCanAdd(a, b, mode);
            });
        }
        runFuzz(30'000, [&] {
            auto a = randomSTAmountPair(rng);
            auto b = randomSTAmountPair(rng);
            return checkCanSub(a, b);
        });
    }

    void
    test_fuzz_round_to_exponent()
    {
        beginCase("LeanSTAmount.fuzz_round_to_exponent", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        std::uniform_int_distribution<int32_t> scaleDist(-110, 10);
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
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
    test_fuzz_get_rate()
    {
        beginCase("LeanSTAmount.fuzz_get_rate", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto& rng = nextRng();
        for (auto mode :
             {Number::RoundingMode::ToNearest,
              Number::RoundingMode::TowardsZero,
              Number::RoundingMode::Downward,
              Number::RoundingMode::Upward})
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(10'000, [&] {
                auto a = randomSTAmountPair(rng);
                auto b = randomSTAmountPair(rng);
                return checkGetRate(a, b, mode);
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
            ok &= checkNe(a, b);
            ok &= checkLt(a, b);
            ok &= checkLe(a, b);
            ok &= checkGt(a, b);
            ok &= checkGe(a, b);
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
        // native operator+ (STAmount(SField, int64)) does not canonicalize, so 10^17 + 10^17 is the
        // exact 2*10^17 with only an int64 guard (well within range).
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kNative, kMaxNative, 0, 0),
            makeSTAmountPair(kNative, kMaxNative, 0, 0),
            m);
        // neg is sign-magnitude and never overflows.
        checkNeg(makeSTAmountPair(kNative, kMaxNative, 0, 0));
        checkNeg(makeSTAmountPair(kNative, kMaxNative, 0, 1));
        // Cross-kind native vs int64 (MPT) is incomparable: both sides error.
        checkLt(makeSTAmountPair(kNative, 100, 0, 0), makeSTAmountPair(kIntegral, 100, 0, 0));

        // MPT operator+ (STAmount(Asset, int64)) canonicalizes: INT64_MAX + 1 wraps to INT64_MIN,
        // then rounds to -9223372036854775800 (under the 2^63-1 ceiling). Both sides agree.
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0),
            makeSTAmountPair(kIntegral, 1, 0, 0),
            m);
        // -INT64_MAX - 1 == INT64_MIN (no int64 wrap). MPT operator+ canonicalizes, rounding the
        // out-of-range magnitude to -9223372036854775800. Both sides agree.
        checkAddSub(
            "sub",
            false,
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 1),
            makeSTAmountPair(kIntegral, 1, 0, 0),
            m);
        checkAddSub(
            "add",
            true,
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0),
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 1),
            m);

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

        // multiply at the maxima.
        checkMultiply(
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0),
            makeSTAmountPair(kIntegral, kMaxIntegral, 0, 0),
            kIntegral,
            m);
        checkMultiply(
            makeSTAmountPair(kFractional, iouMax, eMax, 0),
            makeSTAmountPair(kFractional, iouMax, eMax, 0),
            kFractional,
            m);
        // Integral multiplication precheck overflows (MPT bounds).
        checkMultiply(
            makeSTAmountPair(kIntegral, 3'037'000'500ULL, 0, 0),
            makeSTAmountPair(kIntegral, 3'037'000'500ULL, 0, 0),
            kIntegral,
            m);
        checkMultiply(
            makeSTAmountPair(kIntegral, 9'000'000'000'000'000ULL, 0, 0),
            makeSTAmountPair(kIntegral, 1'000'000ULL, 0, 0),
            kIntegral,
            m);

        // divide at the IOU extremes: huge / tiny quotients.
        checkDivide(
            makeSTAmountPair(kFractional, iouMax, eMax, 0),
            makeSTAmountPair(kFractional, iouMin, eMin, 0),
            kFractional,
            m);
        checkDivide(
            makeSTAmountPair(kFractional, iouMin, eMin, 0),
            makeSTAmountPair(kFractional, iouMax, eMax, 0),
            kFractional,
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
                // u64Max as an integral operand reads back int64-wrapped (mpt() -> -1); the add
                // then canonicalizes like C++, so both kinds agree.
                checkAddSub(
                    "add",
                    true,
                    makeSTAmountPair(nt, u64Max, 0, neg),
                    makeSTAmountPair(nt, u64Max, 0, neg),
                    m);
                checkLt(makeSTAmountPair(nt, u64Max, 0, neg), makeSTAmountPair(nt, 0, 0, neg));
            }
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

    // Integral values staged above INT64_MAX read back as int64 (wrapping) on both sides: C++ via
    // mpt()/getMPTValue, the model via IntAmount (toNumber/canAdd/canSubtract). u64Max -> -1.
    void
    test_integral_int64_wrap()
    {
        beginCase("LeanSTAmount.integral_int64_wrap");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const m = Number::RoundingMode::ToNearest;
        constexpr uint64_t u64Max = std::numeric_limits<uint64_t>::max();

        // u64Max reads back as int64 -1: canAdd(-1, 1) fits, and toNumber wraps identically.
        checkCanAdd(
            makeSTAmountPair(kIntegral, u64Max, 0, 0), makeSTAmountPair(kIntegral, 1, 0, 0), m);
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

    // Finding (FV_M2_2): multiply()/divide() drop the sign before Downward/Upward rounding, so a
    // negative result rounds toward zero instead of toward the correct infinity.
    void
    test_mul_div_negative_rounding()
    {
        beginCase("LeanSTAmount.mul_div_negative_rounding");
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        using M = Number::RoundingMode;

        auto cppSigned = [](STAmount const& s) -> std::int64_t {
            return s.negative() ? -static_cast<std::int64_t>(s.mantissa())
                                : static_cast<std::int64_t>(s.mantissa());
        };
        auto leanSigned = [](LeanSTAmountResult const& r) -> std::int64_t {
            return r.isNegative ? -static_cast<std::int64_t>(r.mValue)
                                : static_cast<std::int64_t>(r.mValue);
        };
        auto oneCase = [&](char const* tag,
                           bool isDiv,
                           STAmountPair const& a,
                           STAmountPair const& b,
                           std::uint8_t nt,
                           M mode,
                           std::int64_t want) {
            Asset const asset = assetForNumericType(nt);
            NumberRoundModeGuard mg(mode);
            STAmount const cpp =
                isDiv ? divide(a.cppSt, b.cppSt, asset) : multiply(a.cppSt, b.cppSt, asset);
            auto const lean = STAmountFFI::fromExcept(leanCall(
                isDiv ? lean_stamount_divide : lean_stamount_multiply,
                STAmountFFI::build(
                    a.leanSt.numericType, a.leanSt.mValue, a.leanSt.mOffset, a.leanSt.isNegative),
                STAmountFFI::build(
                    b.leanSt.numericType, b.leanSt.mValue, b.leanSt.mOffset, b.leanSt.isNegative),
                NumericTypeFFI::build(nt),
                toLeanMode(mode)));
            BEAST_EXPECTS(
                cppSigned(cpp) == want,
                std::string(tag) + " C++ got " + std::to_string(cppSigned(cpp)) + " want " +
                    std::to_string(want));
            BEAST_EXPECTS(
                lean.ok && leanSigned(lean) == want,
                std::string(tag) + " Lean got " + std::to_string(leanSigned(lean)) + " want " +
                    std::to_string(want));
        };

        // IOU. -0.4444444444444444 * 11 = -4.8888888888888884, only Downward reaches ...889.
        STAmountPair const a4 = makeSTAmountPair(kFractional, 4'444'444'444'444'444ULL, -16, 1);
        STAmountPair const eleven = makeSTAmountPair(kFractional, 11ULL, 0, 0);
        STAmountPair const negFour = makeSTAmountPair(kFractional, 4ULL, 0, 1);
        STAmountPair const negSix = makeSTAmountPair(kFractional, 6ULL, 0, 1);
        STAmountPair const nine = makeSTAmountPair(kFractional, 9ULL, 0, 0);
        oneCase(
            "iou mul .4 Near",
            false,
            a4,
            eleven,
            kFractional,
            M::ToNearest,
            -4'888'888'888'888'888LL);
        oneCase(
            "iou mul .4 Down",
            false,
            a4,
            eleven,
            kFractional,
            M::Downward,
            -4'888'888'888'888'889LL);
        oneCase(
            "iou mul .4 Up", false, a4, eleven, kFractional, M::Upward, -4'888'888'888'888'888LL);
        oneCase(
            "iou div .4 Down",
            true,
            negFour,
            nine,
            kFractional,
            M::Downward,
            -4'444'444'444'444'445LL);
        oneCase(
            "iou div .6 Down",
            true,
            negSix,
            nine,
            kFractional,
            M::Downward,
            -6'666'666'666'666'667LL);

        // MPT (integral) and XRP (native) targets: -6.2 * 2 = -12.4, only Downward reaches -13.
        STAmountPair const m62 = makeSTAmountPair(kFractional, 62ULL, -1, 1);
        STAmountPair const two = makeSTAmountPair(kFractional, 2ULL, 0, 0);
        oneCase("mpt mul .4 Down", false, m62, two, kIntegral, M::Downward, -13);
        oneCase("xrp mul .4 Down", false, m62, two, kNative, M::Downward, -13);
    }

private:
    void
    runTests() override
    {
        test_fuzz_mul_round();
        test_fuzz_round_to_exponent();
        test_fuzz_get_rate();
        test_fuzz_compare();
        test_fuzz_neg();
        test_fuzz_unchecked_from_int64();
        test_fuzz_add_sub();
        test_fuzz_accessors();
        test_fuzz_predicates();
        test_fuzz_constructors();
        test_fuzz_multiply_divide();
        test_fuzz_div_round();
        test_known_construction();
        test_known_comparison();
        test_known_arithmetic();
        test_known_rounding();
        test_known_predicates();
        test_known_round_to_exponent();
        test_known_get_rate();
        test_extreme_values();
        test_integral_int64_wrap();

        // Known discrepancies, each fails until the C++ code is fixed.
        // clang-format off
        // test_add_xrp_overflow();          // FV_M2_1: XRP operator+ at INT64_MAX wraps negative
        // test_mul_div_negative_rounding(); // FV_M2_2: negative mul/div rounds the wrong way
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanSTAmount, formal_verification, xrpl);

}  // namespace xrpl::test
