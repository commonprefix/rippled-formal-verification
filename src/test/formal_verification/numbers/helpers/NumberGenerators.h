#pragma once

#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/protocol/IOUAmountFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/IOUAmount.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/MPTAmount.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/UintTypes.h>
#include <xrpl/protocol/XRPAmount.h>

#include <cstdint>
#include <limits>
#include <random>
#include <stdexcept>
#include <string>

namespace xrpl::test::formal_verification {

struct NumberPair
{
    Number cppNum;
    LeanNumber leanNum;
};

struct MPTAmountPair
{
    MPTAmount cppMpt;
    int64_t leanMpt;
};

struct IOUAmountPair
{
    IOUAmount cppIou;
    LeanIOUAmount leanIou;
};

struct STAmountPair
{
    STAmount cppSt;
    LeanSTAmount leanSt;
};

inline int64_t
randomInt64(std::mt19937_64& rng)
{
    return std::uniform_int_distribution<int64_t>{
        std::numeric_limits<int64_t>::min(), std::numeric_limits<int64_t>::max()}(rng);
}

// Lean FFI numericType tag: 0 = native (XRP, 10^17), 1 = int64 for MPT (2^63-1), 2 = fractional
// (IOU).
constexpr uint8_t kNative = 0;
constexpr uint8_t kIntegral = 1;
constexpr uint8_t kFractional = 2;

inline uint8_t
randomNumericType(std::mt19937_64& rng)
{
    return std::uniform_int_distribution<int>{0, 1}(rng) ? kFractional : kIntegral;
}

// All-zero MPTID sentinel; matches Lean's integral placeholder asset.
inline MPTIssue const&
ffiMPTIssue()
{
    static MPTIssue const k{MPTID{}};
    return k;
}

// Each tag maps to the C++ asset with the matching ceiling: native XRP (10^17), an MPT (2^63-1),
// or an IOU (fractional).
inline Asset
assetForNumericType(uint8_t nt)
{
    switch (nt)
    {
        case kNative:
            return Asset{xrpIssue()};
        case kIntegral:
            return Asset{ffiMPTIssue()};
        default:
            return Asset{noIssue()};
    }
}

inline NumberPair
makeNumberPair(bool negative, uint64_t mantissa, int exponent)
{
    return {
        Number{negative, mantissa, exponent, Number::Unchecked{}},
        LeanNumber{negative, mantissa, static_cast<uint64_t>(exponent)}};
}

inline NumberPair
randomNumberPair(uint64_t mantMin, uint64_t mantMax, int expMin, int expMax)
{
    auto& rng = nextRng();
    std::uniform_int_distribution<uint64_t> mantDist(mantMin, mantMax);
    std::uniform_int_distribution<int> expDist(expMin, expMax);
    std::bernoulli_distribution signDist(0.5);
    return makeNumberPair(signDist(rng), mantDist(rng), expDist(rng));
}

// Normalized mantissa range, caller-chosen exponent range.
inline NumberPair
randomNumberPair(int expMin, int expMax)
{
    return randomNumberPair(Number::minMantissa(), Number::kMaxRep, expMin, expMax);
}

inline MPTAmountPair
makeMPTAmountPair(int64_t value)
{
    return {MPTAmount{value}, value};
}

inline MPTAmountPair
randomMPTAmountPair()
{
    return makeMPTAmountPair(randomInt64(nextRng()));
}

// Throws on out-of-canonical-range (m, e); use raw fields for edge fuzz.
inline IOUAmountPair
makeIOUAmountPair(int64_t mantissa, int64_t exponent)
{
    return {IOUAmount{mantissa, static_cast<int>(exponent)}, {mantissa, exponent}};
}

// Canonical-range IOUAmountPair — never throws at construction.
inline IOUAmountPair
randomIOUAmountPair(std::mt19937_64& rng)
{
    std::uniform_int_distribution<uint64_t> mantDist(STAmount::kMinValue, STAmount::kMaxValue);
    std::uniform_int_distribution<int> expDist(STAmount::kMinOffset, STAmount::kMaxOffset);
    std::bernoulli_distribution signDist(0.5);
    uint64_t const mag = mantDist(rng);
    int64_t const mantissa = signDist(rng) ? -static_cast<int64_t>(mag) : static_cast<int64_t>(mag);
    return makeIOUAmountPair(mantissa, static_cast<int64_t>(expDist(rng)));
}

// STAmount::Unchecked ctor - mirrors Lean's decodeSTAmount (no canonicalize).
inline STAmount
stAmountUnchecked(uint8_t nt, uint64_t mValue, int64_t mOffset, uint8_t mIsNegative)
{
    Asset const asset = assetForNumericType(nt);
    return asset.visit(
        [&](Issue const& iss) {
            return STAmount{
                iss,
                static_cast<STAmount::mantissa_type>(mValue),
                static_cast<STAmount::exponent_type>(mOffset),
                mIsNegative != 0,
                STAmount::Unchecked{}};
        },
        [&](MPTIssue const& mpt) {
            return STAmount{
                mpt,
                static_cast<STAmount::mantissa_type>(mValue),
                static_cast<STAmount::exponent_type>(mOffset),
                mIsNegative != 0,
                STAmount::Unchecked{}};
        });
}

inline STAmountPair
makeSTAmountPair(uint8_t nt, uint64_t mValue, int64_t mOffset, uint8_t isNegative)
{
    return {
        stAmountUnchecked(nt, mValue, mOffset, isNegative),
        LeanSTAmount{nt, mValue, mOffset, isNegative}};
}

// When uint64_t to int64 and then negate, we need to prevent -INT64_MIN (-2^63)
inline bool
canSign(uint64_t mv) noexcept
{
    return mv != 0 && mv != (uint64_t{1} << 63);
}

// Broad STAmountPair: integral spans the full uint64 mantissa range (offset 0),
// fractional is 10% canonical zero plus full-uint64 mantissa over [kMinOffset-100, kMaxOffset+100].
inline STAmountPair
randomSTAmountPair(std::mt19937_64& rng, uint8_t nt)
{
    std::bernoulli_distribution sign(0.5);
    std::uniform_int_distribution<uint64_t> mant(0, std::numeric_limits<uint64_t>::max());
    if (nt == kFractional)
    {
        if (std::uniform_int_distribution<int>{0, 9}(rng) == 0)
            return makeSTAmountPair(kFractional, 0, -100, 0);
        std::uniform_int_distribution<int> exp(
            STAmount::kMinOffset - 100, STAmount::kMaxOffset + 100);
        uint64_t const mv = mant(rng);
        return makeSTAmountPair(
            kFractional,
            mv,
            static_cast<int64_t>(exp(rng)),
            static_cast<uint8_t>(canSign(mv) && sign(rng)));
    }
    uint64_t const mv = mant(rng);
    return makeSTAmountPair(kIntegral, mv, 0, static_cast<uint8_t>(canSign(mv) && sign(rng)));
}

inline STAmountPair
randomSTAmountPair(std::mt19937_64& rng)
{
    return randomSTAmountPair(rng, randomNumericType(rng));
}

}  // namespace xrpl::test::formal_verification
