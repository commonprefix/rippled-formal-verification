#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/IOUAmountFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/numbers/helpers/NumberTypes.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/STAmount.h>

#include <cstdint>
#include <limits>
#include <sstream>
#include <string>

namespace xrpl::test::formal_verification {

// Magnitude of an int64 without UB at INT64_MIN.
inline uint64_t
magnitude(int64_t m) noexcept
{
    return m < 0 ? (0u - static_cast<uint64_t>(m)) : static_cast<uint64_t>(m);
}

// Fold a returned Number object into the observable Number.mantissa()/exponent() form.
inline LeanNumberResult
readNumberFields(NumberFFI const& n)
{
    uint64_t mantissa = lean_number_mantissa(n.borrow());
    int64_t exponent = lean_number_exponent(n.borrow());
    uint8_t const negative = lean_number_negative(n.borrow());
    if (mantissa > static_cast<uint64_t>(std::numeric_limits<int64_t>::max()))
    {
        mantissa /= 10;
        ++exponent;
    }
    LeanNumberResult r;
    r.negative = negative;
    r.mantissa = mantissa;
    r.exponent = static_cast<uint64_t>(exponent);
    r.ok = true;
    return r;
}

// Erroring op: `Except String Number`. ok mirrors the Except being `.ok`.
inline LeanNumberResult
readNumberExcept(lean_object* exceptOwned)
{
    LeanExcept<NumberFFI> const e = readExcept<NumberFFI>(exceptOwned);
    if (!e.value)
    {
        LeanNumberResult r{};
        r.ok = false;
        return r;
    }
    return readNumberFields(*e.value);
}

// Pure op (e.g. neg): the Number object directly (never raises), so ok is always true.
inline LeanNumberResult
readNumberObject(lean_object* objOwned)
{
    NumberFFI const obj(objOwned);
    return readNumberFields(obj);
}

// `Except String IOUAmount`: the model IOUAmount fields (a.mantissa/a.exponent) on ok.
inline LeanIOUResult
readIOUExcept(lean_object* exceptOwned)
{
    LeanExcept<IOUAmountFFI> const e = readExcept<IOUAmountFFI>(exceptOwned);
    if (!e.value)
        return LeanIOUResult{0, 0, false};
    LeanIOUResult r;
    r.mantissa = lean_iou_amount_mantissa(e.value->borrow());
    r.exponent = lean_iou_amount_exponent(e.value->borrow());
    r.ok = true;
    return r;
}

// Lean uses sign-magnitude, C++ folds both into a signed mantissa().
inline bool
fieldsEqual(LeanNumberResult const& lean, Number const& cpp)
{
    auto m = cpp.mantissa();
    return lean.mantissa == magnitude(m) && lean.exponent == cpp.exponent() &&
        lean.negative == (m < 0);
}

inline std::string
format(LeanNumberResult const& r)
{
    std::stringstream ss;
    ss << (r.negative ? "-" : "+") << r.mantissa << "e" << r.exponent;
    return ss.str();
}

inline std::string
format(Number const& n)
{
    auto m = n.mantissa();
    std::stringstream ss;
    ss << (m < 0 ? "-" : "+") << magnitude(m) << "e" << n.exponent();
    return ss.str();
}

inline std::string
format(LeanSTAmountResult const& r)
{
    std::stringstream ss;
    ss << "nt=" << static_cast<int>(r.numericType) << " " << (r.isNegative ? "-" : "+") << r.mValue
       << "e" << r.mOffset;
    return ss.str();
}

inline std::string
format(STAmount const& s)
{
    std::stringstream ss;
    int const nt = (s.native() || s.asset().holds<MPTIssue>()) ? 0 : 1;
    ss << "nt=" << nt << " " << (s.negative() ? "-" : "+") << s.mantissa() << "e" << s.exponent();
    return ss.str();
}

}  // namespace xrpl::test::formal_verification
