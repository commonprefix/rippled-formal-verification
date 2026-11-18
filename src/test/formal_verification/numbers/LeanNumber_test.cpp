#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/Int64FFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/numbers/helpers/NumberHelpers.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test.h>

#include <boost/multiprecision/cpp_int.hpp>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <limits>
#include <optional>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

extern "C" {
lean_object*
lean_number_mul(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_div(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_add(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_sub(lean_object*, lean_object*, uint8_t);
lean_object*
lean_number_neg(lean_object*);
int64_t
lean_number_signum(lean_object*);
lean_object*
lean_number_to_rep(lean_object*, uint8_t);
lean_object*
lean_number_normalize(lean_object*, uint8_t);
uint8_t
lean_number_eq(lean_object*, lean_object*);
uint8_t
lean_number_ne(lean_object*, lean_object*);
uint8_t
lean_number_lt(lean_object*, lean_object*);
uint8_t
lean_number_le(lean_object*, lean_object*);
uint8_t
lean_number_gt(lean_object*, lean_object*);
uint8_t
lean_number_ge(lean_object*, lean_object*);
}

namespace xrpl::test {

using namespace formal_verification;

namespace {

// a and b at one exponent.
struct PairCase
{
    std::int64_t a;
    std::int64_t b;
    int exponent;
    TER expected;
};

// a + b at one exponent, and the Number C++ returns.
struct SumCase
{
    std::int64_t a;
    std::int64_t b;
    int exponent;
    ScaledValue expected;
    std::optional<Number::RoundingMode> mode{};
};

// a * 10^ea times b * 10^eb.
struct ProductCase
{
    std::int64_t a;
    std::int64_t b;
    int ea;
    int eb;
    TER expected;
    std::optional<Number::RoundingMode> mode{};
};

// to_rep of mantissa * 10^-1, and the int64 C++ returns.
struct ToRepCase
{
    std::int64_t mantissa;
    std::int64_t expected;
    std::optional<Number::RoundingMode> mode{};
};

// normalize of the sign and unsigned mantissa at exponent.
struct NormalizeCase
{
    bool negative;
    std::uint64_t mantissa;
    int exponent;
    TER expected;
};

std::string
text(PairCase const& c, char op, Number::RoundingMode mode)
{
    return std::to_string(c.a) + ' ' + op + ' ' + std::to_string(c.b) + " at exponent " +
        std::to_string(c.exponent) + ", " + modeName(mode);
}

std::string
text(SumCase const& c, Number::RoundingMode mode)
{
    return text(
        PairCase{.a = c.a, .b = c.b, .exponent = c.exponent, .expected = tesSUCCESS}, '+', mode);
}

std::string
text(ProductCase const& c, Number::RoundingMode mode)
{
    return std::to_string(c.a) + "e" + std::to_string(c.ea) + " * " + std::to_string(c.b) + "e" +
        std::to_string(c.eb) + ", " + modeName(mode);
}

std::string
text(ToRepCase const& c, Number::RoundingMode mode)
{
    return std::to_string(c.mantissa) + "e-1, " + modeName(mode);
}

std::string
text(NormalizeCase const& c, Number::RoundingMode mode)
{
    return (c.negative ? "-" : "") + std::to_string(c.mantissa) + "e" + std::to_string(c.exponent) +
        ", " + modeName(mode);
}

}  // namespace

class LeanNumber_test : public LeanSuite
{
    static std::string
    fmtNum(bool neg, uint64_t m, int e)
    {
        std::stringstream ss;
        ss << (neg ? "-" : "") << m << "e" << e;
        return ss.str();
    }

    static std::string
    fmtNum(NumberPair const& p)
    {
        return fmtNum(p.leanNum.negative != 0, p.leanNum.mantissa, p.cppNum.exponent());
    }

    // Compares both sides; returns the C++ verdict.
    TER
    checkResult(
        std::string const& label,
        LeanNumberResult const& lean,
        Number const& cpp,
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

        if (lean.mantissa == 0 && cpp.mantissa() == 0)
        {
            pass();
            return verdict;
        }

        if (!fieldsEqual(lean, cpp))
        {
            std::stringstream ss;
            ss << label << ": result mismatch lean=" << format(lean) << " cpp=" << format(cpp);
            fail(ss.str());
            return verdict;
        }
        pass();
        return verdict;
    }

    using LeanBinOp = lean_object* (*)(lean_object*, lean_object*, uint8_t);
    using LeanUnaryOp = lean_object* (*)(lean_object*);
    using CppBinOp = std::function<Number(Number const&, Number const&)>;
    using CppUnaryOp = std::function<Number(Number const&)>;

    TER
    checkBinOp(
        std::string const& label,
        LeanBinOp leanOp,
        CppBinOp cppOp,
        NumberPair const& a,
        NumberPair const& b,
        Number::RoundingMode mode)
    {
        auto lean = NumberFFI::fromExcept(leanOp(
            lean_number_build(
                a.leanNum.negative, a.leanNum.mantissa, static_cast<int64_t>(a.leanNum.exponent)),
            lean_number_build(
                b.leanNum.negative, b.leanNum.mantissa, static_cast<int64_t>(b.leanNum.exponent)),
            toLeanMode(mode)));
        bool cppThrew = false;
        Number cpp;
        try
        {
            cpp = cppOp(a.cppNum, b.cppNum);
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        return checkResult(label, lean, cpp, cppThrew);
    }

    TER
    checkUnary(std::string const& label, LeanUnaryOp leanOp, CppUnaryOp cppOp, NumberPair const& x)
    {
        auto lean = NumberFFI::fromObject(leanOp(lean_number_build(
            x.leanNum.negative, x.leanNum.mantissa, static_cast<int64_t>(x.leanNum.exponent))));
        bool cppThrew = false;
        Number cpp;
        try
        {
            cpp = cppOp(x.cppNum);
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        return checkResult(label, lean, cpp, cppThrew);
    }

    TER
    checkNormalize(
        std::string const& label,
        bool neg,
        uint64_t mant,
        int exp,
        Number::RoundingMode mode)
    {
        uint8_t leanMode = toLeanMode(mode);
        auto lean = NumberFFI::fromExcept(lean_number_normalize(
            lean_number_build(neg ? 1 : 0, mant, static_cast<int64_t>(exp)), leanMode));
        bool cppThrew = false;
        Number cpp;
        try
        {
            cpp = Number{neg, mant, exp, Number::Normalized{}};
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        return checkResult(label, lean, cpp, cppThrew);
    }

    std::vector<uint64_t>
    edgeMantissas() const
    {
        uint64_t const minM = Number::minMantissa();
        uint64_t const maxRep = Number::kMaxRep;
        uint64_t const maxM = Number::maxMantissa();
        return {
            minM,
            minM + 1,
            maxRep - 1,
            maxRep,
            Number::kMaxRepUp,
            maxM - maxM % 10,
        };
    }

    std::vector<std::pair<int, int>>
    edgeExpPairs() const
    {
        return {
            {0, 0}, {0, 1}, {0, -1}, {0, 18}, {0, -40}, {40, 40}, {-40, -40}, {80, -96}, {-96, 80}};
    }

    std::vector<int>
    edgeExps() const
    {
        return {0, 1, -1, 18, -18, 40, -40, 80, -96};
    }

    // One operand: ~1/3 a random edge value, else a uniform interior value.
    NumberPair
    randomOperand()
    {
        constexpr double edgeBias = 1.0 / 3;
        auto& rng = nextRng();
        std::bernoulli_distribution useEdge(edgeBias);
        if (useEdge(rng))
        {
            auto const ms = edgeMantissas();
            auto const es = edgeExps();
            std::uniform_int_distribution<std::size_t> mi(0, ms.size() - 1);
            std::uniform_int_distribution<std::size_t> ei(0, es.size() - 1);
            std::bernoulli_distribution sign(0.5);
            return makeNumberPair(sign(rng), ms[mi(rng)], es[ei(rng)]);
        }
        return randomNumberPair(-96, 80);
    }

    // Edge values in operands
    // every edge mantissa, both signs, paired against every other,
    // over the curated exponent relationships and all rounding modes.
    void
    runOperandEdges(LeanBinOp leanOp, char opChar, CppBinOp cppOp)
    {
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);

        auto operandsAt = [this](int e) {
            std::vector<NumberPair> ops;
            for (uint64_t m : edgeMantissas())
                for (bool neg : {false, true})
                    ops.push_back(makeNumberPair(neg, m, e));
            return ops;
        };

        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            for (auto const& [ea, eb] : edgeExpPairs())
                for (auto const& a : operandsAt(ea))
                    for (auto const& b : operandsAt(eb))
                        checkBinOp(
                            fmtNum(a) + ' ' + opChar + ' ' + fmtNum(b), leanOp, cppOp, a, b, mode);
        }
    }

    // Safety net for inputs the targeted tests never thought to try: random
    // operands, edge or interior, to catch divergences anywhere else.
    void
    runFuzzBinOp(LeanBinOp leanOp, char opChar, CppBinOp cppOp, int iterations = 10'000)
    {
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            runFuzz(iterations, [&] {
                auto a = randomOperand();
                auto b = randomOperand();
                std::string label = fmtNum(a) + ' ' + opChar + ' ' + fmtNum(b);
                return checkBinOp(label, leanOp, cppOp, a, b, mode);
            });
        }
    }

    // A named group of (ea, eb) input-exponent pairs for runResultExpRegions.
    struct ResultRegion
    {
        char const* name;
        std::vector<std::pair<int, int>> exps;
    };

    // Walk the target result exponent over [center-radius, center+radius]; toExps
    // maps each target to the (ea, eb) that lands this op's result there.
    static std::vector<std::pair<int, int>>
    resultExpRange(int center, int radius, std::function<std::pair<int, int>(int)> toExps)
    {
        std::vector<std::pair<int, int>> out;
        for (int r = center - radius; r <= center + radius; ++r)
            out.push_back(toExps(r));
        return out;
    }

    // Test edge result exponents
    // The mantissa is pinned to minMantissa so only the exponent moves; each
    // region's (ea,eb) pairs steer the result exponent (mul: ea+eb+18, div: ea-eb)
    // into normal / under- / over-flow, in both signs and all rounding modes.
    void
    runResultExpRegions(
        char opChar,
        LeanBinOp leanOp,
        CppBinOp cppOp,
        std::vector<ResultRegion> const& regions)
    {
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        uint64_t const m = Number::minMantissa();
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            for (auto const& region : regions)
                for (auto const& [ea, eb] : region.exps)
                    for (bool na : {false, true})
                        for (bool nb : {false, true})
                        {
                            auto a = makeNumberPair(na, m, ea);
                            auto b = makeNumberPair(nb, m, eb);
                            checkBinOp(
                                std::string(region.name) + ": " + fmtNum(a) + ' ' + opChar + ' ' +
                                    fmtNum(b),
                                leanOp,
                                cppOp,
                                a,
                                b,
                                mode);
                        }
        }
    }

    static boost::multiprecision::cpp_int
    pow10(int n)
    {
        boost::multiprecision::cpp_int r = 1;
        while (n-- > 0)
            r *= 10;
        return r;
    }

    // b such that a * b lands near (resultNeg ? -1 : 1) * resultMant * 10^resultExp.
    static NumberPair
    mulFactor(NumberPair const& a, uint64_t resultMant, int resultExp, bool resultNeg)
    {
        using boost::multiprecision::cpp_int;
        int constexpr scale = 40;
        cpp_int q = cpp_int(resultMant) * pow10(scale) / cpp_int(a.leanNum.mantissa);
        int exp = resultExp - a.cppNum.exponent() - scale;
        cpp_int const hi = pow10(19);
        while (q >= hi)
        {
            q /= 10;
            ++exp;
        }
        uint64_t mant = static_cast<uint64_t>(q);
        if (mant > Number::kMaxRep)
            mant -= mant % 10;
        bool const bNeg = (a.leanNum.negative != 0) != resultNeg;
        return makeNumberPair(bNeg, mant, exp);
    }

    static NumberPair
    divFactor(NumberPair const& a, uint64_t resultMant, int resultExp, bool resultNeg)
    {
        using boost::multiprecision::cpp_int;
        int constexpr scale = 40;
        cpp_int q = cpp_int(a.leanNum.mantissa) * pow10(scale) / cpp_int(resultMant);
        int exp = a.cppNum.exponent() - resultExp - scale;
        cpp_int const hi = pow10(19);
        while (q >= hi)
        {
            q /= 10;
            ++exp;
        }
        uint64_t mant = static_cast<uint64_t>(q);
        if (mant > Number::kMaxRep)
            mant -= mant % 10;
        bool const bNeg = (a.leanNum.negative != 0) != resultNeg;
        return makeNumberPair(bNeg, mant, exp);
    }

    // Walk the result mantissa across [lo, hi] at a fixed result exponent and
    // both result signs; a's exponent is pinned near resultExp/2 so the derived
    // partner stays in range.
    void
    runResultMantissaRange(
        char opChar,
        LeanBinOp leanOp,
        CppBinOp cppOp,
        std::function<NumberPair(NumberPair const&, uint64_t, int, bool)> partner,
        uint64_t lo,
        uint64_t hi,
        int resultExp)
    {
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        std::uniform_int_distribution<uint64_t> mantDist(Number::minMantissa(), Number::kMaxRep);
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            for (uint64_t t = lo; t <= hi; ++t)
                for (bool neg : {false, true})
                    for (int i = 0; i < 8; ++i)
                    {
                        auto a = makeNumberPair(false, mantDist(nextRng()), resultExp / 2);
                        auto b = partner(a, t, resultExp, neg);
                        checkBinOp(
                            fmtNum(a) + ' ' + opChar + ' ' + fmtNum(b), leanOp, cppOp, a, b, mode);
                    }
        }
    }

    void
    runSumCusp(char opChar, LeanBinOp leanOp, CppBinOp cppOp, bool flipB)
    {
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        uint64_t const minM = Number::minMantissa();
        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};
            for (int e : {0, 40, -40})
                for (uint64_t t = Number::kMaxRep - 7; t <= Number::kMaxRepUp + 13; ++t)
                    for (bool aNeg : {false, true})
                    {
                        auto a = makeNumberPair(aNeg, minM, e);
                        auto b = makeNumberPair(aNeg != flipB, t - minM, e);
                        checkBinOp(
                            fmtNum(a) + ' ' + opChar + ' ' + fmtNum(b), leanOp, cppOp, a, b, mode);
                    }
        }
    }

    // signum has no error channel; Lean returns Int64, C++ returns int.
    bool
    checkSignum(std::string const& label, NumberPair const& x)
    {
        int64_t lean = lean_number_signum(lean_number_build(
            x.leanNum.negative, x.leanNum.mantissa, static_cast<int64_t>(x.leanNum.exponent)));
        int cpp = x.cppNum.signum();
        if (lean != cpp)
        {
            std::stringstream ss;
            ss << "signum(" << label << "): lean=" << lean << " cpp=" << cpp;
            fail(ss.str());
            return false;
        }
        pass();
        return true;
    }

    using LeanCmpOp = uint8_t (*)(lean_object*, lean_object*);

    // Verify Lean and C++ agree on every relational operator for one pair.
    // Comparisons can't error, so we compare the raw bool results directly.
    bool
    checkCompare(std::string const& label, NumberPair const& a, NumberPair const& b)
    {
        auto leanCmp = [&](LeanCmpOp op) {
            return op(lean_number_build(
                          a.leanNum.negative,
                          a.leanNum.mantissa,
                          static_cast<int64_t>(a.leanNum.exponent)),
                      lean_number_build(
                          b.leanNum.negative,
                          b.leanNum.mantissa,
                          static_cast<int64_t>(b.leanNum.exponent))) != 0;
        };
        struct Case
        {
            char const* sym;
            bool lean;
            bool cpp;
        };
        Case const cases[] = {
            {"==", leanCmp(lean_number_eq), a.cppNum == b.cppNum},
            {"!=", leanCmp(lean_number_ne), a.cppNum != b.cppNum},
            {"<", leanCmp(lean_number_lt), a.cppNum < b.cppNum},
            {"<=", leanCmp(lean_number_le), a.cppNum <= b.cppNum},
            {">", leanCmp(lean_number_gt), a.cppNum > b.cppNum},
            {">=", leanCmp(lean_number_ge), a.cppNum >= b.cppNum},
        };
        bool ok = true;
        for (auto const& c : cases)
        {
            if (c.lean != c.cpp)
            {
                std::stringstream ss;
                ss << label << ' ' << c.sym << ": lean=" << c.lean << " cpp=" << c.cpp;
                fail(ss.str());
                ok = false;
            }
        }
        if (ok)
            pass();
        return ok;
    }

public:
    void
    testMul()
    {
        beginCase("LeanNumber.mul", true);
        auto const mul = [](Number const& a, Number const& b) { return a * b; };

        runOperandEdges(lean_number_mul, '*', mul);

        // Input exponents whose mul result lands at exponent r (ea + eb + 18 = r)..
        auto const mulExps = [](int r) -> std::pair<int, int> {
            int const s = r - 18;  // result exp = ea + eb + 18
            return {s / 2, s - (s / 2)};
        };

        runResultExpRegions(
            '*',
            lean_number_mul,
            mul,
            {
                {"normal", {{0, 0}, {18, -18}, {-40, 40}}},
                {"near-underflow", resultExpRange(Number::kMinExponent, 5, mulExps)},
                {"underflow", {{-20000, -20000}}},
                {"near-overflow", resultExpRange(Number::kMaxExponent, 5, mulExps)},
                {"overflow", {{20000, 20000}}},
            });

        uint64_t const minM = Number::minMantissa();
        uint64_t const maxM = Number::maxMantissa();
        // Walk the result mantissa across the cusp, at mid, top, and bottom exponents.
        for (int e : {0, Number::kMaxExponent, Number::kMinExponent})
            runResultMantissaRange(
                '*',
                lean_number_mul,
                mul,
                mulFactor,
                Number::kMaxRep - 7,
                Number::kMaxRepUp + 13,
                e);

        // Land at maxMantissa (top of range) at kMax: there a round-up carries past
        // it, and only at kMax does that carry tip the exponent into overflow.
        runResultMantissaRange(
            '*', lean_number_mul, mul, mulFactor, maxM - 20, maxM, Number::kMaxExponent);

        // Land at minMantissa (bottom of range) at kMin: there a value below it gets
        // shifted down, and only at kMin does that shift tip the exponent into underflow.
        runResultMantissaRange(
            '*', lean_number_mul, mul, mulFactor, minM - 3, minM + 3, Number::kMinExponent);

        runFuzzBinOp(lean_number_mul, '*', mul);
    }

    void
    testDiv()
    {
        beginCase("LeanNumber.div", true);
        auto const div = [](Number const& a, Number const& b) { return a / b; };

        runOperandEdges(lean_number_div, '/', div);

        auto const divExps = [](int r) -> std::pair<int, int> {
            int const s = r + 18;
            return {s / 2, s / 2 - s};
        };

        runResultExpRegions(
            '/',
            lean_number_div,
            div,
            {
                {"normal", {{0, 0}, {18, -18}, {-40, 40}}},
                {"near-underflow", resultExpRange(Number::kMinExponent, 5, divExps)},
                {"underflow", {{-20000, 20000}}},
                {"near-overflow", resultExpRange(Number::kMaxExponent, 5, divExps)},
                {"overflow", {{20000, -20000}}},
            });

        uint64_t const minM = Number::minMantissa();
        uint64_t const maxM = Number::maxMantissa();
        for (int e : {0, Number::kMaxExponent, Number::kMinExponent})
            runResultMantissaRange(
                '/',
                lean_number_div,
                div,
                divFactor,
                Number::kMaxRep - 7,
                Number::kMaxRepUp + 13,
                e);

        runResultMantissaRange(
            '/', lean_number_div, div, divFactor, maxM - 20, maxM, Number::kMaxExponent);

        runResultMantissaRange(
            '/', lean_number_div, div, divFactor, minM - 3, minM + 3, Number::kMinExponent);

        runFuzzBinOp(lean_number_div, '/', div);

        // Only the canonical zero (Number{}, exp=INT_MIN) is a zero divisor in
        // C++ operator/=; it is the one divisor the non-zero cases cannot reach.
        {
            auto lean = NumberFFI::fromExcept(lean_number_div(
                lean_number_build(false, 1'000'000'000'000'000'000ULL, 0),
                lean_number_build(
                    false, 0, static_cast<int64_t>(std::numeric_limits<int>::lowest())),
                0));
            bool cppThrew = false;
            Number cpp;
            try
            {
                cpp =
                    Number{false, 1'000'000'000'000'000'000ULL, 0, Number::Unchecked{}} / Number{};
            }
            catch (std::overflow_error const&)
            {
                cppThrew = true;
            }
            checkResult("div by canonical zero", lean, cpp, cppThrew);
        }
    }

    void
    testAdd()
    {
        beginCase("LeanNumber.add", true);
        auto const add = [](Number const& a, Number const& b) { return a + b; };
        runOperandEdges(lean_number_add, '+', add);
        runSumCusp('+', lean_number_add, add, false);
        runFuzzBinOp(lean_number_add, '+', add);
    }

    void
    testSub()
    {
        beginCase("LeanNumber.sub", true);
        auto const sub = [](Number const& a, Number const& b) { return a - b; };
        runOperandEdges(lean_number_sub, '-', sub);
        runSumCusp('-', lean_number_sub, sub, true);
        runFuzzBinOp(lean_number_sub, '-', sub);
    }

    void
    testNeg()
    {
        beginCase("LeanNumber.neg", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto const neg = [](Number const& x) { return -x; };

        for (uint64_t m : edgeMantissas())
            for (bool n : {false, true})
                for (int e : edgeExps())
                {
                    auto a = makeNumberPair(n, m, e);
                    checkUnary("neg(" + fmtNum(a) + ")", lean_number_neg, neg, a);
                }
        checkUnary("neg(0)", lean_number_neg, neg, makeNumberPair(false, 0, 0));

        runFuzz(10'000, [&] {
            auto a = randomOperand();
            return checkUnary("neg(" + fmtNum(a) + ")", lean_number_neg, neg, a);
        });
    }

    void
    testSignum()
    {
        beginCase("LeanNumber.signum", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);

        for (uint64_t m : edgeMantissas())
            for (bool n : {false, true})
                for (int e : edgeExps())
                    checkSignum(fmtNum(makeNumberPair(n, m, e)), makeNumberPair(n, m, e));
        checkSignum("+zero", makeNumberPair(false, 0, 0));
        checkSignum("-zero", makeNumberPair(true, 0, 0));

        runFuzz(10'000, [&] {
            auto a = randomOperand();
            return checkSignum(fmtNum(a), a);
        });
    }

    void
    testNormalize()
    {
        beginCase("LeanNumber.normalize", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        uint64_t const minM = Number::minMantissa();

        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};

            for (uint64_t m = Number::kMaxRep - 7; m <= Number::kMaxRepUp + 13; ++m)
                for (bool neg : {false, true})
                    for (int e : {0, 1, -1, 40})
                        checkNormalize("normalize(" + fmtNum(neg, m, e) + ")", neg, m, e, mode);

            for (uint64_t m = minM - 3; m <= minM + 3; ++m)
                for (bool neg : {false, true})
                    for (int e : {0, 1, -1, 40})
                        checkNormalize("normalize(" + fmtNum(neg, m, e) + ")", neg, m, e, mode);

            // Non-normal inputs only normalize() may see.
            std::vector<uint64_t> normMants = edgeMantissas();
            for (uint64_t m :
                 {Number::kMaxRep + 1,
                  Number::kMaxRep + 2,
                  uint64_t{9'999'999'999'999'999'999ULL},
                  minM - 1,
                  uint64_t{1},
                  uint64_t{0}})
                normMants.push_back(m);
            for (uint64_t m : normMants)
                for (bool neg : {false, true})
                    for (int e : edgeExps())
                        checkNormalize("normalize(" + fmtNum(neg, m, e) + ")", neg, m, e, mode);

            runFuzz(10'000, [&] {
                auto p = randomNumberPair(1, 9'999'999'999'999'999'999ULL, -132800, 132800);
                bool neg = p.leanNum.negative != 0;
                int exp = p.cppNum.exponent();
                std::string label = "normalize(" + fmtNum(neg, p.leanNum.mantissa, exp) + ")";
                return checkNormalize(label, neg, p.leanNum.mantissa, exp, mode);
            });
        }
    }

    void
    testCompare()
    {
        beginCase("LeanNumber.compare", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);
        auto const ms = edgeMantissas();
        auto const exps = edgeExpPairs();

        for (uint64_t ma : ms)
            for (bool na : {false, true})
                for (uint64_t mb : ms)
                    for (bool nb : {false, true})
                        for (auto const& [ea, eb] : exps)
                        {
                            auto a = makeNumberPair(na, ma, ea);
                            auto b = makeNumberPair(nb, mb, eb);
                            checkCompare(fmtNum(a) + " ? " + fmtNum(b), a, b);
                        }
        for (uint64_t m : ms)
            for (bool n : {false, true})
                checkCompare(
                    "0 ? " + fmtNum(makeNumberPair(n, m, 0)),
                    makeNumberPair(false, 0, 0),
                    makeNumberPair(n, m, 0));

        runFuzz(10'000, [&] {
            auto a = randomOperand();
            auto b = randomOperand();
            bool ok = checkCompare(fmtNum(a) + " ? " + fmtNum(b), a, b);
            ok = checkCompare(fmtNum(a) + " ? self", a, a) && ok;
            return ok;
        });
    }

    TER
    checkToRep(std::string const& label, NumberPair const& x, Number::RoundingMode mode)
    {
        auto const lean = readExcept<Int64FFI>(lean_number_to_rep(
            lean_number_build(
                x.leanNum.negative, x.leanNum.mantissa, static_cast<int64_t>(x.leanNum.exponent)),
            toLeanMode(mode)));
        bool cppThrew = false;
        std::int64_t cpp = 0;
        try
        {
            cpp = static_cast<std::int64_t>(x.cppNum);
        }
        catch (std::overflow_error const&)
        {
            cppThrew = true;
        }
        TER const verdict = cppVerdict(cppThrew, !cppThrew && cpp == 0);
        if (lean.value.has_value() == cppThrew)
        {
            fail(label + ": error mismatch");
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
            ss << label << ": lean=" << lean.value->read() << " cpp=" << cpp;
            fail(ss.str());
            return verdict;
        }
        pass();
        return verdict;
    }

    void
    testToRep()
    {
        beginCase("LeanNumber.to_rep", true);
        NumberMantissaScaleGuard sg(MantissaRange::MantissaScale::Large330);

        std::vector<std::pair<bool, std::pair<uint64_t, int>>> const fractions = {
            {false, {15, -1}},
            {false, {25, -1}},
            {false, {14, -1}},
            {false, {16, -1}},
            {true, {15, -1}},
            {true, {25, -1}},
            {false, {5, -1}},
            {false, {1, 5}}};

        for (auto mode : kRoundingModes)
        {
            SaveNumberRoundMode save{Number::setround(mode)};

            for (uint64_t m : edgeMantissas())
                for (bool n : {false, true})
                    for (int e : edgeExps())
                    {
                        auto a = makeNumberPair(n, m, e);
                        checkToRep("to_rep(" + fmtNum(a) + ")", a, mode);
                    }
            for (auto const& [n, me] : fractions)
            {
                auto a = makeNumberPair(n, me.first, me.second);
                checkToRep("to_rep(" + fmtNum(a) + ")", a, mode);
            }

            runFuzz(10'000, [&] {
                auto a = randomOperand();
                return checkToRep("to_rep(" + fmtNum(a) + ")", a, mode);
            });
        }
    }

    TER
    checkOp(
        char opChar,
        LeanBinOp leanOp,
        CppBinOp const& cppOp,
        NumberPair const& a,
        NumberPair const& b,
        Number::RoundingMode mode)
    {
        return checkBinOp(fmtNum(a) + ' ' + opChar + ' ' + fmtNum(b), leanOp, cppOp, a, b, mode);
    }

    TER
    checkSum(std::int64_t a, std::int64_t b, int exponent, Number::RoundingMode mode)
    {
        return checkOp(
            '+',
            lean_number_add,
            [](Number const& x, Number const& y) { return x + y; },
            makeNumberPair(a, exponent),
            makeNumberPair(b, exponent),
            mode);
    }

    TER
    checkDifference(PairCase const& c, Number::RoundingMode mode)
    {
        return checkOp(
            '-',
            lean_number_sub,
            [](Number const& x, Number const& y) { return x - y; },
            makeNumberPair(c.a, c.exponent),
            makeNumberPair(c.b, c.exponent),
            mode);
    }

    TER
    checkProduct(ProductCase const& c, Number::RoundingMode mode)
    {
        return checkOp(
            '*',
            lean_number_mul,
            [](Number const& x, Number const& y) { return x * y; },
            makeNumberPair(c.a, c.ea),
            makeNumberPair(c.b, c.eb),
            mode);
    }

    // One test case per list; each row compares Lean with C++, then the C++ result with the row.
    void
    testBoundaries()
    {
        auto const sum = [&](std::size_t i, PairCase const& c, Number::RoundingMode mode) {
            expectResult(i, text(c, '+', mode), checkSum(c.a, c.b, c.exponent, mode), c.expected);
        };
        auto const difference = [&](std::size_t i, PairCase const& c, Number::RoundingMode mode) {
            expectResult(i, text(c, '-', mode), checkDifference(c, mode), c.expected);
        };
        auto const roundedSum = [&](std::size_t i, SumCase const& c, Number::RoundingMode mode) {
            checkSum(c.a, c.b, c.exponent, mode);
            Number const r =
                makeNumberPair(c.a, c.exponent).cppNum + makeNumberPair(c.b, c.exponent).cppNum;
            expectResult(i, text(c, mode), ScaledValue{r.mantissa(), r.exponent()}, c.expected);
        };
        auto const product = [&](std::size_t i, ProductCase const& c, Number::RoundingMode mode) {
            expectResult(i, text(c, mode), checkProduct(c, mode), c.expected);
        };
        auto const toRep = [&](std::size_t i, ToRepCase const& c, Number::RoundingMode mode) {
            auto const x = makeNumberPair(c.mantissa, -1);
            checkToRep("to_rep(" + fmtNum(x) + ")", x, mode);
            expectResult(i, text(c, mode), static_cast<std::int64_t>(x.cppNum), c.expected);
        };
        auto const normalize =
            [&](std::size_t i, NormalizeCase const& c, Number::RoundingMode mode) {
                TER const verdict = checkNormalize(
                    "normalize(" + fmtNum(c.negative, c.mantissa, c.exponent) + ")",
                    c.negative,
                    c.mantissa,
                    c.exponent,
                    mode);
                expectResult(i, text(c, mode), verdict, c.expected);
            };

        runRows(*this, "LeanNumber.add overflow", kSumOverflow, sum);
        runRows(*this, "LeanNumber.sub overflow", kDifferenceOverflow, difference);
        runRows(*this, "LeanNumber.add rounding", kSumRounding, roundedSum);
        runRows(*this, "LeanNumber.sub underflow", kDifferenceUnderflow, difference);
        runRows(*this, "LeanNumber.mul overflow", kProductOverflow, product);
        runRows(*this, "LeanNumber.mul underflow", kProductUnderflow, product);
        runRows(*this, "LeanNumber.mul underflow, by mode", kProductUnderflowByMode, product);
        runRows(*this, "LeanNumber.to_rep half", kToRepHalf, toRep);
        runRows(*this, "LeanNumber.normalize bounds", kNormalizeBounds, normalize);
    }

private:
    // Each list runs its rows under every rounding mode on the large mantissa scale; a row that
    // names a mode runs under that mode only, as its result depends on the mode. A group comment
    // names the row on the cusp; its rows move both operands (or mantissa and exponent) around it.
    // kMaxRep is 9'223'372'036'854'775'807 and kMaxRepUp 9'223'372'036'854'775'810.
    // - kSumOverflow: add at exponent 32'768. A sum of magnitude up to kMaxRepUp fits; above it
    //   the add throws (tecPATH_DRY) in every mode, even where the mode would round it to
    //   kMaxRepUp.
    // - kDifferenceOverflow: sub of opposite signs at exponent 32'768, the same sums and verdicts.
    // - kSumRounding: the same sums at exponent -32'768. A sum past kMaxRep never throws; the mode
    //   picks kMaxRep or a multiple of 10 (reported as 18 digits, exponent + 1). The rows hold the
    //   Number C++ returns.
    // - kDifferenceUnderflow: sub at exponent -32'768. a - b down to 10^18 is a value; below it
    //   the result needs a lower exponent and is zero (tecPRECISION_LOSS) in every mode.
    // - kProductOverflow: mul with result exponent 32'768. A product up to kMaxRepUp * 10^18 fits
    //   in every mode, one whose 19 leading digits pass kMaxRepUp throws (tecPATH_DRY). The
    //   commented rows break that rule: C++ and the model round first and succeed where the mode
    //   rounds the product down to kMaxRepUp.
    // - kProductUnderflow: mul with result exponent -32'768. A product that rounds to 10^37 or
    //   more is a value, below that it is zero (tecPRECISION_LOSS). Just under 10^37 the mode
    //   decides (kProductUnderflowByMode).
    // - kToRepHalf: to_rep of m * 10^-1 around an exact half; the mode picks the integer, ToNearest
    //   half to even. The rows hold the int64 C++ returns.
    // - kNormalizeBounds: normalize at exponent 32'768 fits a mantissa up to kMaxRepUp and throws
    //   above it (tecPATH_DRY); at -32'768 a mantissa below 10^18, or any lower exponent, is zero
    //   (tecPRECISION_LOSS).
    // clang-format off
    static constexpr PairCase kSumOverflow[] = {
        // 1'000'000'000'000'000'000 + 8'223'372'036'854'775'810 at exponent 32'768
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'809, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'810, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'809, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'810, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'809, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'810, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        // 8'223'372'036'854'775'810 + 1'000'000'000'000'000'000 at exponent 32'768
        {.a = 8'223'372'036'854'775'808, .b = 1'000'000'000'000'000'000, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'808, .b = 1'000'000'000'000'000'001, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'808, .b = 1'000'000'000'000'000'002, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'809, .b = 1'000'000'000'000'000'000, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'809, .b = 1'000'000'000'000'000'001, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'809, .b = 1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'810, .b = 1'000'000'000'000'000'000, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'810, .b = 1'000'000'000'000'000'001, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'810, .b = 1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'811, .b = 1'000'000'000'000'000'000, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'811, .b = 1'000'000'000'000'000'001, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'811, .b = 1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'812, .b = 1'000'000'000'000'000'000, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'812, .b = 1'000'000'000'000'000'001, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'812, .b = 1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        // 4'611'686'018'427'387'905 + 4'611'686'018'427'387'905 at exponent 32'768
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        // -1'000'000'000'000'000'000 + -8'223'372'036'854'775'810 at exponent 32'768
        {.a = -1'000'000'000'000'000'002, .b = -8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'002, .b = -8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'002, .b = -8'223'372'036'854'775'810, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'002, .b = -8'223'372'036'854'775'809, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'002, .b = -8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'001, .b = -8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'001, .b = -8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'001, .b = -8'223'372'036'854'775'810, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'001, .b = -8'223'372'036'854'775'809, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'001, .b = -8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'000, .b = -8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'000, .b = -8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'000, .b = -8'223'372'036'854'775'810, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'000, .b = -8'223'372'036'854'775'809, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'000, .b = -8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        // -4'611'686'018'427'387'905 + -4'611'686'018'427'387'905 at exponent 32'768
        {.a = -4'611'686'018'427'387'907, .b = -4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'907, .b = -4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'907, .b = -4'611'686'018'427'387'905, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'907, .b = -4'611'686'018'427'387'904, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'907, .b = -4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'906, .b = -4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'906, .b = -4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'906, .b = -4'611'686'018'427'387'905, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'906, .b = -4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'906, .b = -4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'905, .b = -4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'905, .b = -4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'905, .b = -4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'905, .b = -4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'905, .b = -4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = -4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'904, .b = -4'611'686'018'427'387'906, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = -4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = -4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = -4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = -4'611'686'018'427'387'907, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = -4'611'686'018'427'387'906, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = -4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = -4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = -4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
    };
    static constexpr PairCase kDifferenceOverflow[] = {
        // -1'000'000'000'000'000'000 - 8'223'372'036'854'775'810 at exponent 32'768
        {.a = -1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'809, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'810, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'809, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'810, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'808, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'809, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'810, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'811, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'812, .exponent = 32'768, .expected = tecPATH_DRY},
        // -4'611'686'018'427'387'905 - 4'611'686'018'427'387'905 at exponent 32'768
        {.a = -4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'907, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'906, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = -4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'903, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'904, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'905, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'906, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = -4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'907, .exponent = 32'768, .expected = tesSUCCESS},
        // 8'223'372'036'854'775'810 - -1'000'000'000'000'000'000 at exponent 32'768
        {.a = 8'223'372'036'854'775'808, .b = -1'000'000'000'000'000'002, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'808, .b = -1'000'000'000'000'000'001, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'808, .b = -1'000'000'000'000'000'000, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'809, .b = -1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'809, .b = -1'000'000'000'000'000'001, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'809, .b = -1'000'000'000'000'000'000, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'810, .b = -1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'810, .b = -1'000'000'000'000'000'001, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'810, .b = -1'000'000'000'000'000'000, .exponent = 32'768, .expected = tesSUCCESS},
        {.a = 8'223'372'036'854'775'811, .b = -1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'811, .b = -1'000'000'000'000'000'001, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'811, .b = -1'000'000'000'000'000'000, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'812, .b = -1'000'000'000'000'000'002, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'812, .b = -1'000'000'000'000'000'001, .exponent = 32'768, .expected = tecPATH_DRY},
        {.a = 8'223'372'036'854'775'812, .b = -1'000'000'000'000'000'000, .exponent = 32'768, .expected = tecPATH_DRY},
    };
    static constexpr SumCase kSumRounding[] = {
        // 1'000'000'000'000'000'000 + 8'223'372'036'854'775'807 at exponent -32'768
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'805, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'805, .exponent = -32'768}},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'806, .exponent = -32'768}},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'000, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'805, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'806, .exponent = -32'768}},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'001, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'805, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'002, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'582, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        // 4'611'686'018'427'387'903 + 4'611'686'018'427'387'904 at exponent -32'768
        {.a = 4'611'686'018'427'387'901, .b = 4'611'686'018'427'387'902, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'803, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'901, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'804, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'901, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'805, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'901, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'806, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'901, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'902, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'804, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'805, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'806, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'902, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'902, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'805, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'806, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'903, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'902, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'806, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 4'611'686'018'427'387'904, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'902, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'903, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 9'223'372'036'854'775'807, .exponent = -32'768}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'904, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'905, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'581, .exponent = -32'767}, .mode = Number::RoundingMode::Downward},
        {.a = 4'611'686'018'427'387'905, .b = 4'611'686'018'427'387'906, .exponent = -32'768, .expected = {.mantissa = 922'337'203'685'477'582, .exponent = -32'767}, .mode = Number::RoundingMode::Upward},
    };
    static constexpr PairCase kDifferenceUnderflow[] = {
        // 2'000'000'000'000'000'000 - 1'000'000'000'000'000'000 at exponent -32'768
        {.a = 1'999'999'999'999'999'998, .b = 1'000'000'000'000'000'000, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999'998, .b = 1'000'000'000'000'000'001, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999'998, .b = 1'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999'999, .b = 1'000'000'000'000'000'000, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999'999, .b = 1'000'000'000'000'000'001, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999'999, .b = 1'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'000'000, .b = 1'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'000, .b = 1'000'000'000'000'000'001, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'000'000, .b = 1'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'000'001, .b = 1'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'001, .b = 1'000'000'000'000'000'001, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'001, .b = 1'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'000'002, .b = 1'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'002, .b = 1'000'000'000'000'000'001, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'002, .b = 1'000'000'000'000'000'002, .exponent = -32'768, .expected = tesSUCCESS},
        // 9'223'372'036'854'775'807 - 8'223'372'036'854'775'807 at exponent -32'768
        {.a = 9'223'372'036'854'775'805, .b = 8'223'372'036'854'775'805, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'805, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'805, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'805, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'805, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'806, .b = 8'223'372'036'854'775'805, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'806, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'806, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'806, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'806, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'807, .b = 8'223'372'036'854'775'805, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'807, .b = 8'223'372'036'854'775'806, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'807, .b = 8'223'372'036'854'775'807, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'807, .b = 8'223'372'036'854'775'808, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 9'223'372'036'854'775'807, .b = 8'223'372'036'854'775'809, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        // 5'000'000'000'000'000'000 - 4'000'000'000'000'000'000 at exponent -32'768
        {.a = 4'999'999'999'999'999'998, .b = 3'999'999'999'999'999'998, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999'998, .b = 3'999'999'999'999'999'999, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'998, .b = 4'000'000'000'000'000'000, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'998, .b = 4'000'000'000'000'000'001, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'998, .b = 4'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'999, .b = 3'999'999'999'999'999'998, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999'999, .b = 3'999'999'999'999'999'999, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999'999, .b = 4'000'000'000'000'000'000, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'999, .b = 4'000'000'000'000'000'001, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'999, .b = 4'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000'000, .b = 3'999'999'999'999'999'998, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'000, .b = 3'999'999'999'999'999'999, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'000, .b = 4'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'000, .b = 4'000'000'000'000'000'001, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000'000, .b = 4'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000'001, .b = 3'999'999'999'999'999'998, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'001, .b = 3'999'999'999'999'999'999, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'001, .b = 4'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'001, .b = 4'000'000'000'000'000'001, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'001, .b = 4'000'000'000'000'000'002, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000'002, .b = 3'999'999'999'999'999'998, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'002, .b = 3'999'999'999'999'999'999, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'002, .b = 4'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'002, .b = 4'000'000'000'000'000'001, .exponent = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'002, .b = 4'000'000'000'000'000'002, .exponent = -32'768, .expected = tesSUCCESS},
    };
    static constexpr ProductCase kProductOverflow[] = {
        // 1'000'000'000'000'000'000e32'750 * 9'223'372'036'854'775'807e0
        {.a = 1'000'000'000'000'000'000, .b = 9'223'372'036'854'775'805, .ea = 32'750, .eb = 0, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'000, .b = 9'223'372'036'854'775'806, .ea = 32'750, .eb = 0, .expected = tesSUCCESS},
        {.a = 1'000'000'000'000'000'000, .b = 9'223'372'036'854'775'807, .ea = 32'750, .eb = 0, .expected = tesSUCCESS},
        // {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'805, .ea = 32'750, .eb = 0, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'805, .ea = 32'750, .eb = 0, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'805, .ea = 32'750, .eb = 0, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'805, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'806, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        // {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'806, .ea = 32'750, .eb = 0, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'806, .ea = 32'750, .eb = 0, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'806, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'807, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        // {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'807, .ea = 32'750, .eb = 0, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'807, .ea = 32'750, .eb = 0, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 1'000'000'000'000'000'001, .b = 9'223'372'036'854'775'807, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 1'000'000'000'000'000'002, .b = 9'223'372'036'854'775'805, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'002, .b = 9'223'372'036'854'775'806, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY},
        {.a = 1'000'000'000'000'000'002, .b = 9'223'372'036'854'775'807, .ea = 32'750, .eb = 0, .expected = tecPATH_DRY},
        // 9'223'372'036'854'775'807e0 * 1'000'000'000'000'000'000e32'750
        {.a = 9'223'372'036'854'775'805, .b = 1'000'000'000'000'000'000, .ea = 0, .eb = 32'750, .expected = tesSUCCESS},
        // {.a = 9'223'372'036'854'775'805, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 9'223'372'036'854'775'805, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 9'223'372'036'854'775'805, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 9'223'372'036'854'775'805, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 9'223'372'036'854'775'805, .b = 1'000'000'000'000'000'002, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY},
        {.a = 9'223'372'036'854'775'806, .b = 1'000'000'000'000'000'000, .ea = 0, .eb = 32'750, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'806, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        // {.a = 9'223'372'036'854'775'806, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 9'223'372'036'854'775'806, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 9'223'372'036'854'775'806, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 9'223'372'036'854'775'806, .b = 1'000'000'000'000'000'002, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY},
        {.a = 9'223'372'036'854'775'807, .b = 1'000'000'000'000'000'000, .ea = 0, .eb = 32'750, .expected = tesSUCCESS},
        {.a = 9'223'372'036'854'775'807, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        // {.a = 9'223'372'036'854'775'807, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 9'223'372'036'854'775'807, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 9'223'372'036'854'775'807, .b = 1'000'000'000'000'000'001, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 9'223'372'036'854'775'807, .b = 1'000'000'000'000'000'002, .ea = 0, .eb = 32'750, .expected = tecPATH_DRY},
        // 3'037'000'499'976'049'692e16'375 * 3'037'000'499'976'049'693e16'375
        {.a = 3'037'000'499'976'049'690, .b = 3'037'000'499'976'049'691, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'690, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'690, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'690, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'690, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'691, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        // {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'691, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'691, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        // {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        // {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'692, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'691, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'693, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'691, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'692, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'693, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::ToNearest},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::TowardsZero},
        // {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tesSUCCESS, .mode = Number::RoundingMode::Downward},
        {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'694, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY, .mode = Number::RoundingMode::Upward},
        {.a = 3'037'000'499'976'049'694, .b = 3'037'000'499'976'049'695, .ea = 16'375, .eb = 16'375, .expected = tecPATH_DRY},
    };
    static constexpr ProductCase kProductUnderflow[] = {
        // 2'000'000'000'000'000'000e-32'768 * 5'000'000'000'000'000'000e-19
        {.a = 1'999'999'999'999'999'998, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999'998, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS},
        {.a = 2'000'000'000'000'000'000, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'000, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'000, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'001, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'001, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'001, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'001, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'001, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'002, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'002, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'002, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'002, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        {.a = 2'000'000'000'000'000'002, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tesSUCCESS},
        // 5'000'000'000'000'000'000e-19 * 2'000'000'000'000'000'000e-32'768
        {.a = 4'999'999'999'999'999'998, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'998, .b = 2'000'000'000'000'000'001, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999'998, .b = 2'000'000'000'000'000'002, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999'999, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 4'999'999'999'999'999'999, .b = 2'000'000'000'000'000'001, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 4'999'999'999'999'999'999, .b = 2'000'000'000'000'000'002, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'000, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS},
        {.a = 5'000'000'000'000'000'000, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'000, .b = 2'000'000'000'000'000'001, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'000, .b = 2'000'000'000'000'000'002, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'001, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'001, .b = 2'000'000'000'000'000'001, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'001, .b = 2'000'000'000'000'000'002, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'002, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'002, .b = 2'000'000'000'000'000'001, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        {.a = 5'000'000'000'000'000'002, .b = 2'000'000'000'000'000'002, .ea = -19, .eb = -32'768, .expected = tesSUCCESS},
        // 3'162'277'660'168'379'331e-16'393 * 3'162'277'660'168'379'331e-16'394
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS},
    };
    static constexpr ProductCase kProductUnderflowByMode[] = {
        // 2'000'000'000'000'000'000e-32'768 * 5'000'000'000'000'000'000e-19
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 1'999'999'999'999'999'998, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 1'999'999'999'999'999'999, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'000, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'001, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 1'999'999'999'999'999'999, .b = 5'000'000'000'000'000'002, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'998, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 2'000'000'000'000'000'000, .b = 4'999'999'999'999'999'999, .ea = -32'768, .eb = -19, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        // 5'000'000'000'000'000'000e-19 * 2'000'000'000'000'000'000e-32'768
        {.a = 4'999'999'999'999'999'998, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'999'999'999'999'999'998, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'999'999'999'999'999'998, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 4'999'999'999'999'999'998, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 4'999'999'999'999'999'998, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'999'999'999'999'999'998, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'999'999'999'999'999'998, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 4'999'999'999'999'999'998, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 4'999'999'999'999'999'999, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'999'999'999'999'999'999, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'999'999'999'999'999'999, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 4'999'999'999'999'999'999, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 4'999'999'999'999'999'999, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 4'999'999'999'999'999'999, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 4'999'999'999'999'999'999, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 4'999'999'999'999'999'999, .b = 2'000'000'000'000'000'000, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 5'000'000'000'000'000'000, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 5'000'000'000'000'000'000, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 5'000'000'000'000'000'000, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 5'000'000'000'000'000'000, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 5'000'000'000'000'000'001, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'998, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 5'000'000'000'000'000'002, .b = 1'999'999'999'999'999'999, .ea = -19, .eb = -32'768, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        // 3'162'277'660'168'379'331e-16'393 * 3'162'277'660'168'379'331e-16'394
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'329, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'330, .b = 3'162'277'660'168'379'333, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'331, .b = 3'162'277'660'168'379'332, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'332, .b = 3'162'277'660'168'379'331, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'329, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::ToNearest},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::TowardsZero},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tecPRECISION_LOSS, .mode = Number::RoundingMode::Downward},
        {.a = 3'162'277'660'168'379'333, .b = 3'162'277'660'168'379'330, .ea = -16'393, .eb = -16'394, .expected = tesSUCCESS, .mode = Number::RoundingMode::Upward},
    };
    static constexpr ToRepCase kToRepHalf[] = {
        // 1'000'000'000'000'000'005e-1
        {.mantissa = 1'000'000'000'000'000'003, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'003, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'003, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'003, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'004, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'004, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'004, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'004, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'005, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'005, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'005, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'005, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'006, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'006, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'006, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'006, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'007, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'007, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'007, .expected = 100'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'007, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        // 1'000'000'000'000'000'015e-1
        {.mantissa = 1'000'000'000'000'000'013, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'013, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'013, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'013, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'014, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'014, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'014, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'014, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'015, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'015, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'015, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'015, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'016, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'016, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'016, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'016, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::Upward},
        {.mantissa = 1'000'000'000'000'000'017, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 1'000'000'000'000'000'017, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 1'000'000'000'000'000'017, .expected = 100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = 1'000'000'000'000'000'017, .expected = 100'000'000'000'000'002, .mode = Number::RoundingMode::Upward},
        // 5'000'000'000'000'000'005e-1
        {.mantissa = 5'000'000'000'000'000'003, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 5'000'000'000'000'000'003, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 5'000'000'000'000'000'003, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 5'000'000'000'000'000'003, .expected = 500'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 5'000'000'000'000'000'004, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 5'000'000'000'000'000'004, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 5'000'000'000'000'000'004, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 5'000'000'000'000'000'004, .expected = 500'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 5'000'000'000'000'000'005, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 5'000'000'000'000'000'005, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 5'000'000'000'000'000'005, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 5'000'000'000'000'000'005, .expected = 500'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 5'000'000'000'000'000'006, .expected = 500'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 5'000'000'000'000'000'006, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 5'000'000'000'000'000'006, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 5'000'000'000'000'000'006, .expected = 500'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = 5'000'000'000'000'000'007, .expected = 500'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 5'000'000'000'000'000'007, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 5'000'000'000'000'000'007, .expected = 500'000'000'000'000'000, .mode = Number::RoundingMode::Downward},
        {.mantissa = 5'000'000'000'000'000'007, .expected = 500'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        // 9'223'372'036'854'775'805e-1
        {.mantissa = 9'223'372'036'854'775'803, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'223'372'036'854'775'803, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'223'372'036'854'775'803, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'223'372'036'854'775'803, .expected = 922'337'203'685'477'581, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'223'372'036'854'775'804, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'223'372'036'854'775'804, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'223'372'036'854'775'804, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'223'372'036'854'775'804, .expected = 922'337'203'685'477'581, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'223'372'036'854'775'805, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'223'372'036'854'775'805, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'223'372'036'854'775'805, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'223'372'036'854'775'805, .expected = 922'337'203'685'477'581, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'223'372'036'854'775'806, .expected = 922'337'203'685'477'581, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'223'372'036'854'775'806, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'223'372'036'854'775'806, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'223'372'036'854'775'806, .expected = 922'337'203'685'477'581, .mode = Number::RoundingMode::Upward},
        {.mantissa = 9'223'372'036'854'775'807, .expected = 922'337'203'685'477'581, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = 9'223'372'036'854'775'807, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = 9'223'372'036'854'775'807, .expected = 922'337'203'685'477'580, .mode = Number::RoundingMode::Downward},
        {.mantissa = 9'223'372'036'854'775'807, .expected = 922'337'203'685'477'581, .mode = Number::RoundingMode::Upward},
        // -1'000'000'000'000'000'005e-1
        {.mantissa = -1'000'000'000'000'000'007, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'007, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'007, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'007, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'006, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'006, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'006, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'006, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'005, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'005, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'005, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'005, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'004, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'004, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'004, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'004, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'003, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'003, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'003, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'003, .expected = -100'000'000'000'000'000, .mode = Number::RoundingMode::Upward},
        // -1'000'000'000'000'000'015e-1
        {.mantissa = -1'000'000'000'000'000'017, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'017, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'017, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'017, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'016, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'016, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'016, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'016, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'015, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'015, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'015, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'015, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'014, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'014, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'014, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'014, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
        {.mantissa = -1'000'000'000'000'000'013, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::ToNearest},
        {.mantissa = -1'000'000'000'000'000'013, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::TowardsZero},
        {.mantissa = -1'000'000'000'000'000'013, .expected = -100'000'000'000'000'002, .mode = Number::RoundingMode::Downward},
        {.mantissa = -1'000'000'000'000'000'013, .expected = -100'000'000'000'000'001, .mode = Number::RoundingMode::Upward},
    };
    static constexpr NormalizeCase kNormalizeBounds[] = {
        // 9'223'372'036'854'775'810e32'768
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'768, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'768, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'768, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        // -9'223'372'036'854'775'810e32'768
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'768, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'808ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'768, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'809ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'768, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'810ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'811ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = true, .mantissa = 9'223'372'036'854'775'812ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        // 9'999'999'999'999'999'999e32'768
        {.negative = false, .mantissa = 9'999'999'999'999'999'997ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999'997ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999'997ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'997ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'997ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'998ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999'998ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999'998ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'998ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'998ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'999ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999'999ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 9'999'999'999'999'999'999ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'999ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 9'999'999'999'999'999'999ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000'000ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000'000ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000'000ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000'000ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000'000ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000'001ULL, .exponent = 32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000'001ULL, .exponent = 32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 10'000'000'000'000'000'001ULL, .exponent = 32'768, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000'001ULL, .exponent = 32'769, .expected = tecPATH_DRY},
        {.negative = false, .mantissa = 10'000'000'000'000'000'001ULL, .exponent = 32'770, .expected = tecPATH_DRY},
        // 1'000'000'000'000'000'000e-32'768
        {.negative = false, .mantissa = 999'999'999'999'999'998, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999'998, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999'998, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999'998, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 999'999'999'999'999'998, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 999'999'999'999'999'999, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999'999, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999'999, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 999'999'999'999'999'999, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 999'999'999'999'999'999, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'768, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'768, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'766, .expected = tesSUCCESS},
        // -1'000'000'000'000'000'000e-32'768
        {.negative = true, .mantissa = 999'999'999'999'999'998, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999'998, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999'998, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999'998, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 999'999'999'999'999'998, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 999'999'999'999'999'999, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999'999, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999'999, .exponent = -32'768, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 999'999'999'999'999'999, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 999'999'999'999'999'999, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'768, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'000, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'768, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'001, .exponent = -32'766, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'770, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'769, .expected = tecPRECISION_LOSS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'768, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'767, .expected = tesSUCCESS},
        {.negative = true, .mantissa = 1'000'000'000'000'000'002, .exponent = -32'766, .expected = tesSUCCESS},
        // 1e-32'750
        {.negative = false, .mantissa = 0, .exponent = -32'752, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = -32'751, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = -32'750, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = -32'749, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 0, .exponent = -32'748, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1, .exponent = -32'752, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1, .exponent = -32'751, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 1, .exponent = -32'750, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1, .exponent = -32'749, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 1, .exponent = -32'748, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 2, .exponent = -32'752, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 2, .exponent = -32'751, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 2, .exponent = -32'750, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 2, .exponent = -32'749, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 2, .exponent = -32'748, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 3, .exponent = -32'752, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 3, .exponent = -32'751, .expected = tecPRECISION_LOSS},
        {.negative = false, .mantissa = 3, .exponent = -32'750, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 3, .exponent = -32'749, .expected = tesSUCCESS},
        {.negative = false, .mantissa = 3, .exponent = -32'748, .expected = tesSUCCESS},
    };
    // clang-format on
    void
    runTests() override
    {
        testMul();
        testDiv();
        testAdd();
        testSub();
        testNeg();
        testSignum();
        testNormalize();
        testCompare();
        testToRep();
        testBoundaries();
    }
};

BEAST_DEFINE_TESTSUITE(LeanNumber, formal_verification, xrpl);

}  // namespace xrpl::test
