#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/formal_verification/tx/lending/LoanSetSweepCases.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <exception>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

// Differential tests of the broker cover transactions: LoanBrokerCoverDeposit, CoverWithdraw and
// CoverClawback. Each compares preclaim (the `can*` TER), doApply (the TER and the broker's
// post-state) and the amount moved.
class LeanLoanBrokerCover_test : public LeanSuite
{
    enum class Op : std::uint8_t { deposit, withdraw, clawback };

    static std::string
    opName(Op op)
    {
        switch (op)
        {
            case Op::deposit:
                return "cover deposit";
            case Op::withdraw:
                return "cover withdraw";
            case Op::clawback:
                return "cover clawback";
        }
        return "?";
    }

    void
    expectTer(TER lean, TER cpp, TER expected, char const* what)
    {
        BEAST_EXPECTS(
            cpp == expected,
            std::string(what) + " cpp=" + transToken(cpp) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            lean == expected,
            std::string(what) + " lean=" + transToken(lean) + " expected " + transToken(expected));
    }

    // The shared ledgers (one per asset) the staged single-value tests and the sweeps run on.
    struct SweepLedger
    {
        jtx::Env* env;
        BrokerFixture f;
    };
    std::optional<SweepLedger> iou_;
    std::optional<SweepLedger> mpt_;

    SweepLedger&
    ledger(LendingAsset kind)
    {
        return kind == LendingAsset::mpt ? *mpt_ : *iou_;
    }

    static std::string
    assetName(SweepLedger const& l)
    {
        return l.f.asset.raw().holds<MPTIssue>() ? "MPT" : "IOU";
    }

    // Run one cover transaction on `view` (already staged). `amount` is the transaction amount;
    // for a clawback `nullopt` omits sfAmount (claw everything above the minimum cover).
    // `expectedMoved` is the cover movement both sides must agree on. Returns the C++ verdict.
    TER
    checkCover(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        Op op,
        std::optional<Number> const& amount,
        std::optional<TER> expected,
        std::optional<Number> const& expectedMoved,
        std::string const& at)
    {
        using namespace jtx;
        LoanBroker const before = loan_set_sweep::readBroker(view, f);
        Vault const pool = readVaultState(view, f.vaultKeylet, f.asset.raw());
        std::optional<STAmount> const stAmount =
            amount ? std::optional<STAmount>{f.asset(*amount)} : std::nullopt;

        // The model's doApply assumes preclaim passed (a failed precondition there is
        // tecINTERNAL), so it is only run when the model's preclaim accepts.
        LawfulTerResult can{};
        std::optional<LeanCoverResult> result;
        switch (op)
        {
            case Op::deposit:
                can = leanCanCoverDeposit(before, pool, *stAmount);
                if (can.ter == tesSUCCESS)
                    result = leanCoverDeposit(before, pool, *stAmount);
                break;
            case Op::withdraw:
                can = leanCanCoverWithdraw(before, pool, *stAmount);
                if (can.ter == tesSUCCESS)
                    result = leanCoverWithdraw(before, pool, *stAmount);
                break;
            case Op::clawback:
                can = leanCanCoverClawback(before, pool, stAmount);
                if (can.ter == tesSUCCESS)
                    result = leanCoverClawback(before, pool, stAmount);
                break;
        }
        expectLawful(can);

        json::Value tx;
        switch (op)
        {
            case Op::deposit:
                tx = loan_broker::coverDeposit(f.owner, f.brokerKeylet.key, *stAmount);
                break;
            case Op::withdraw:
                tx = loan_broker::coverWithdraw(f.owner, f.brokerKeylet.key, *stAmount);
                break;
            case Op::clawback:
                tx = loan_broker::coverClawback(f.issuer);
                tx[sfLoanBrokerID] = to_string(f.brokerKeylet.key);
                if (stAmount)
                    tx[sfAmount] = stAmount->getJson(JsonOptions::Values::None);
                break;
        }
        TER const cppTer = loan_set_sweep::applyOn(env, view, tx);
        LoanBroker const cpp = loan_set_sweep::readBroker(view, f);

        TER lean = can.ter;
        if (can.leanError || (can.ter == tesSUCCESS && (!result || result->leanError)))
            lean = tefEXCEPTION;
        else if (can.ter == tesSUCCESS)
            lean = result->error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            lean == cppTer, at + ": lean=" + transToken(lean) + " cpp=" + transToken(cppTer));
        if (expected)
            expectTer(lean, cppTer, *expected, "cover");
        if (cppTer != tesSUCCESS || lean != tesSUCCESS)
            return cppTer;

        BEAST_EXPECTS(
            result->broker.coverAvailable == cpp.coverAvailable,
            at + ": coverAvailable lean=" + to_string(result->broker.coverAvailable) +
                " cpp=" + to_string(cpp.coverAvailable));
        BEAST_EXPECTS(
            result->broker.debtTotal == cpp.debtTotal && result->broker.loanCount == cpp.loanCount,
            at + ": debt or loan count changed");
        Number const cppMoved = op == Op::deposit ? cpp.coverAvailable - before.coverAvailable
                                                  : before.coverAvailable - cpp.coverAvailable;
        BEAST_EXPECTS(
            Number{result->amount} == cppMoved,
            at + ": moved lean=" + to_string(Number{result->amount}) +
                " cpp=" + to_string(cppMoved));
        if (expectedMoved)
        {
            BEAST_EXPECTS(
                cppMoved == *expectedMoved,
                at + ": moved " + to_string(cppMoved) + " expected " + to_string(*expectedMoved));
        }
        return cppTer;
    }

    // Stage `s` (the vault in its investment phase) on a throwaway view of the shared ledger and
    // run the cover transaction there.
    TER
    checkStagedCover(
        SweepLedger& l,
        loan_set_sweep::LendingStage s,
        Op op,
        std::optional<Number> const& amount,
        std::optional<TER> expected = std::nullopt,
        std::optional<Number> const& expectedMoved = std::nullopt)
    {
        std::string const at = opName(op) + " " + loan_set_sweep::stageText(s) + " amount " +
            (amount ? to_string(*amount) : std::string{"none"});
        OpenView view{*l.env->current()};
        auto const phase = loan_set_sweep::investment(view);
        s.subscriptionDate = phase.subscriptionDate;
        s.redemptionDate = phase.redemptionDate;
        try
        {
            loan_set_sweep::stageLending(*l.env, view, l.f, s);
        }
        catch (std::exception const& e)
        {
            fail(at + ": " + e.what());
            return tefINTERNAL;
        }
        return checkCover(*l.env, l.f, view, op, amount, expected, expectedMoved, at);
    }

    // `n` (in asset units) as grid units of the shared ledger's vault.
    static std::int64_t
    toUnits(SweepLedger const& l, Number const& n)
    {
        return static_cast<std::int64_t>(
            n * Number{1, static_cast<int>(l.env->le(l.f.vaultKeylet)->at(sfScale))});
    }

    // A broker with `cover` deposited and, with `withLoan`, a loan of 1000 (minimum cover 100 at
    // the 10% rate), staged on the shared ledger of the asset like the default fixture broker
    // (1% management fee, 10% / 20% cover rates).
    void
    runCover(
        std::string const& label,
        Op op,
        Number const& cover,
        bool withLoan,
        std::optional<Number> const& amount,
        TER expected,
        std::optional<Number> const& expectedMoved = std::nullopt,
        LendingAsset assetKind = LendingAsset::iou)
    {
        testcase(opName(op) + ": " + label);
        SweepLedger& l = ledger(assetKind);
        loan_set_sweep::LendingStage s{
            .cover = toUnits(l, cover), .managementFeeRate = 1'000, .coverRate = 10'000};
        if (withLoan)
            s.debt = toUnits(l, Number{1'000});
        checkStagedCover(l, s, op, amount, expected, expectedMoved);
    }

    // ---- Sweeps ---------------------------------------------------------------------------------

    // Grid units of the shared ledger's vault, as a transaction amount.
    static Number
    units(SweepLedger const& l, std::int64_t n)
    {
        return loan_set_sweep::units(*l.env->current(), l.f, n);
    }

    // A cover deposit that truncates to zero grid units is tecPRECISION_LOSS. One grid step is
    // written with a 16-digit mantissa (1e15 at exponent -21), so a smaller mantissa truncates
    // to nothing (IOU).
    void
    testCoverDepositSubGridSweep()
    {
        SweepLedger& l = *iou_;
        beginCase(("cover deposit " + assetName(l) + " sub-grid-Sweep").c_str());
        runAroundCusp(
            loan_set_sweep::kSubGridDepositCases, [&](loan_set_sweep::SubGridCusp const& c) {
                return checkStagedCover(
                    l, {.cover = c.cover}, Op::deposit, Number{c.mantissa, -21});
            });
    }

    // A cover deposit past the open limit (cover + amount > 9e15 units) is tecLIMIT_EXCEEDED.
    // Rows put cover + amount exactly on the limit (IOU: the owner holds 1e16 units).
    void
    testCoverOpenLimitSweep()
    {
        SweepLedger& l = *iou_;
        beginCase(("cover deposit " + assetName(l) + " open limit-Sweep").c_str());
        runAroundCusp(
            loan_set_sweep::kCoverOpenLimitCases, [&](loan_set_sweep::CoverAmountCusp const& c) {
                return checkStagedCover(l, {.cover = c.cover}, Op::deposit, units(l, c.amount));
            });
    }

    // A cover withdrawal or clawback that truncates to zero grid units is tecPRECISION_LOSS
    // (IOU; mantissa as in the deposit sweep).
    void
    testCoverTakeSubGridSweep()
    {
        SweepLedger& l = *iou_;
        for (Op const op : {Op::withdraw, Op::clawback})
        {
            beginCase((opName(op) + " " + assetName(l) + " sub-grid-Sweep").c_str());
            runAroundCusp(
                loan_set_sweep::kSubGridTakeCases, [&](loan_set_sweep::SubGridCusp const& c) {
                    return checkStagedCover(l, {.cover = c.cover}, op, Number{c.mantissa, -21});
                });
        }
    }

    void
    testCoverWithdrawAllSweep()
    {
        sweepCoverWithdrawAll(*iou_);
        sweepCoverWithdrawAll(*mpt_);
    }

    // Withdrawing more than the cover is tecINSUFFICIENT_FUNDS. Rows withdraw the whole cover of
    // a broker without debt.
    void
    sweepCoverWithdrawAll(SweepLedger& l)
    {
        beginCase(("cover withdraw " + assetName(l) + " whole cover-Sweep").c_str());
        runAroundCusp(
            loan_set_sweep::kCoverWithdrawAllCases, [&](loan_set_sweep::CoverAmountCusp const& c) {
                return checkStagedCover(l, {.cover = c.cover}, Op::withdraw, units(l, c.amount));
            });
    }

    void
    testMinimumCoverSweep()
    {
        sweepMinimumCover(*iou_);
        sweepMinimumCover(*mpt_);
    }

    // A withdrawal leaving less than the minimum cover ceil(debt * rate / 1e5) is
    // tecINSUFFICIENT_FUNDS. Rows leave exactly the minimum.
    void
    sweepMinimumCover(SweepLedger& l)
    {
        beginCase(("cover withdraw " + assetName(l) + " minimum cover-Sweep").c_str());
        runAroundCusp(
            loan_set_sweep::kMinimumCoverCases, [&](loan_set_sweep::MinimumCoverCusp const& c) {
                return checkStagedCover(
                    l,
                    {.debt = c.debt, .cover = c.cover, .coverRate = c.rate},
                    Op::withdraw,
                    units(l, c.amount));
            });
    }

    void
    testNoExcessSweep()
    {
        sweepNoExcess(*iou_);
        sweepNoExcess(*mpt_);
    }

    // A clawback (no amount) with no cover above the minimum cover is tecINSUFFICIENT_FUNDS; one
    // unit of excess is clawed. Rows hold exactly the minimum cover.
    void
    sweepNoExcess(SweepLedger& l)
    {
        beginCase(("cover clawback " + assetName(l) + " no excess-Sweep").c_str());
        runAroundCusp(
            loan_set_sweep::kNoExcessCases, [&](loan_set_sweep::MinimumCoverCusp const& c) {
                return checkStagedCover(
                    l,
                    {.debt = c.debt, .cover = c.cover, .coverRate = c.rate},
                    Op::clawback,
                    std::nullopt);
            });
    }

    void
    runTests() override
    {
        jtx::Env iouEnv(*this);
        iou_ = SweepLedger{
            .env = &iouEnv, .f = loan_set_sweep::setUpSweepBroker(iouEnv, LendingAsset::iou)};
        jtx::Env mptEnv(*this);
        mpt_ = SweepLedger{
            .env = &mptEnv, .f = loan_set_sweep::setUpSweepBroker(mptEnv, LendingAsset::mpt)};

        // The IOU vault has scale 6, so the cover grid is 1e-6 and the open limit 9e9.
        Number const grid{1, -6};
        Number const openLimit{kOpenLimitUnits, -6};

        // Deposits
        runCover(
            "first deposit", Op::deposit, Number{0}, false, Number{100}, tesSUCCESS, Number{100});
        runCover(
            "second deposit", Op::deposit, Number{100}, false, Number{50}, tesSUCCESS, Number{50});
        runCover(
            "off-grid amount is truncated",
            Op::deposit,
            Number{100},
            false,
            Number{1'234'567, -7},
            tesSUCCESS,
            Number{123'456, -6});
        // covered by testCoverDepositSubGridSweep
        runCover(
            "sub-grid dust", Op::deposit, Number{100}, false, Number{1, -7}, tecPRECISION_LOSS);
        runCover(
            "up to the open limit",
            Op::deposit,
            Number{0},
            false,
            openLimit,
            tesSUCCESS,
            openLimit);
        runCover(
            "17-digit cover leaves the base exponent",
            Op::deposit,
            Number{0},
            false,
            Number{1, 10},
            tecLIMIT_EXCEEDED);
        // covered by testCoverOpenLimitSweep
        runCover(
            "past the open limit",
            Op::deposit,
            Number{0},
            false,
            openLimit + grid,
            tecLIMIT_EXCEEDED);

        // Withdrawals
        runCover("partial", Op::withdraw, Number{100}, false, Number{40}, tesSUCCESS, Number{40});
        runCover(
            "everything", Op::withdraw, Number{100}, false, Number{100}, tesSUCCESS, Number{100});
        // covered by testCoverWithdrawAllSweep
        runCover(
            "more than available",
            Op::withdraw,
            Number{100},
            false,
            Number{101},
            tecINSUFFICIENT_FUNDS);
        // covered by testCoverTakeSubGridSweep
        runCover(
            "sub-grid dust", Op::withdraw, Number{100}, false, Number{1, -7}, tecPRECISION_LOSS);
        runCover(
            "down to the minimum cover",
            Op::withdraw,
            Number{200},
            true,
            Number{100},
            tesSUCCESS,
            Number{100});
        // covered by testMinimumCoverSweep
        runCover(
            "below the minimum cover",
            Op::withdraw,
            Number{200},
            true,
            Number{150},
            tecINSUFFICIENT_FUNDS);

        // Clawbacks by the issuer
        runCover(
            "no amount claws everything",
            Op::clawback,
            Number{100},
            false,
            std::nullopt,
            tesSUCCESS,
            Number{100});
        runCover(
            "zero amount claws everything",
            Op::clawback,
            Number{100},
            false,
            Number{0},
            tesSUCCESS,
            Number{100});
        runCover("partial", Op::clawback, Number{100}, false, Number{40}, tesSUCCESS, Number{40});
        runCover(
            "above the excess is clamped",
            Op::clawback,
            Number{100},
            false,
            Number{150},
            tesSUCCESS,
            Number{100});
        runCover(
            "only the excess over the minimum cover",
            Op::clawback,
            Number{200},
            true,
            std::nullopt,
            tesSUCCESS,
            Number{100});
        runCover(
            "clamped to the excess over the minimum cover",
            Op::clawback,
            Number{200},
            true,
            Number{150},
            tesSUCCESS,
            Number{100});
        // covered by testNoExcessSweep
        runCover(
            "no excess cover", Op::clawback, Number{0}, false, std::nullopt, tecINSUFFICIENT_FUNDS);
        // covered by testCoverTakeSubGridSweep
        runCover(
            "sub-grid dust", Op::clawback, Number{100}, false, Number{1, -7}, tecPRECISION_LOSS);

        // An MPT cover is integral: no rounding to the cover grid.
        auto const mpt = LendingAsset::mpt;
        runCover("MPT", Op::deposit, Number{0}, false, Number{100}, tesSUCCESS, Number{100}, mpt);
        runCover("MPT", Op::withdraw, Number{100}, false, Number{40}, tesSUCCESS, Number{40}, mpt);
        runCover("MPT", Op::clawback, Number{100}, false, Number{40}, tesSUCCESS, Number{40}, mpt);
        runCover(
            "MPT excess over the minimum cover",
            Op::clawback,
            Number{200},
            true,
            std::nullopt,
            tesSUCCESS,
            Number{100},
            mpt);

        // Sweeps
        testCoverDepositSubGridSweep();
        testCoverOpenLimitSweep();
        testCoverTakeSubGridSweep();
        testCoverWithdrawAllSweep();
        testMinimumCoverSweep();
        testNoExcessSweep();
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanBrokerCover, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
