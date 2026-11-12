#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/formal_verification/tx/lending/LoanSetSweepCases.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <exception>
#include <optional>
#include <stdexcept>
#include <string>

namespace xrpl::test::formal_verification {

// Differential tests of LoanSet (one-step and two-step), LoanAccept and LoanDelete. Each case
// compares the model's preclaim TER, then (when preclaim accepts) its doApply TER and the loan,
// vault and broker post-states.
class LeanLoanSet_test : public LeanSuite
{
    std::optional<SweepLedger> iou_;
    std::optional<SweepLedger> mpt_;

    SweepLedger&
    ledger(LendingAsset kind)
    {
        return kind == LendingAsset::mpt ? *mpt_ : *iou_;
    }

    static TER
    leanVerdict(LawfulTerResult const& can, std::optional<LeanLoanResult> const& result)
    {
        if (can.leanError || (result && result->leanError))
            return tefEXCEPTION;
        return modelVerdict(can, result ? result->error : std::nullopt);
    }

    // LoanSet for `p` on `view` (already staged) and in the model on the same pre-state: equal
    // verdicts (and `expected`, when given), and on success equal loan, vault, broker and amount to
    // the borrower.
    TER
    checkLoanSet(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        LoanParams const& p,
        std::optional<TER> expected,
        std::string const& at)
    {
        LoanBroker const broker = readBroker(view, f);
        Vault const pool = readVaultState(view, f.vaultKeylet, f.asset.raw());
        LoanSetArgs const args = loanSetArgs(p);
        std::uint32_t const closeTime = view.header().closeTime.time_since_epoch().count();
        bool const twoStep = p.startDate.has_value();

        LawfulTerResult const can = leanCanLoanCreate(
            broker, pool, args, closeTime, view.parentCloseTime().time_since_epoch().count());
        expectLawful(can);
        Loan const like = loanTemplate(broker, p, twoStep ? *p.startDate : closeTime);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS && !can.leanError)
            result = leanLoanCreate(broker, pool, args, closeTime, like);

        Keylet const loanKeylet = nextLoan(view, f);
        zeroIouBalance(view, f.borrower, f.asset.raw());
        Number const borrowerBefore = holding(view, f.borrower, f.asset.raw());
        TER const cppTer = applyLoanSet(env, view, f, p);
        if (isTemMalformed(cppTer))
        {
            // A preflight-only rule is a loan invariant in the model: the create is not lawful.
            BEAST_EXPECTS(
                leanLoanCreate(broker, pool, args, closeTime, like).leanError ==
                    LeanError::notLawful,
                at + ": cpp=" + transToken(cppTer) + " but the model creates the loan");
            return cppTer;
        }
        TER const lean = leanVerdict(can, result);
        BEAST_EXPECTS(
            lean == cppTer, at + ": cpp=" + transToken(cppTer) + " lean=" + transToken(lean));
        if (expected)
            expectTer(*this, lean, cppTer, *expected);
        if (cppTer != tesSUCCESS || lean != tesSUCCESS)
            return cppTer;
        expectLoanMatches(*this, result->loan, readLoan(view, loanKeylet, f, p));
        expectSameVault(
            *this, "vault ", result->pool, readVaultState(view, f.vaultKeylet, f.asset.raw()));
        expectBrokerMatches(*this, result->loan.broker, readBroker(view, f));
        expectNumber(
            *this,
            "amount to borrower",
            result->amountToBorrower,
            holding(view, f.borrower, f.asset.raw()) - borrowerBefore);
        return cppTer;
    }

    // Stage `s` on a throwaway view of `env`, then check the LoanSet there.
    TER
    checkLoanSet(
        jtx::Env& env,
        BrokerFixture const& f,
        LendingStage const& s,
        LoanParams const& p,
        std::optional<TER> expected = std::nullopt)
    {
        std::string const at = stageText(s) + " P " + to_string(p.principal) + " N " +
            std::to_string(p.paymentTotal) + " I " + std::to_string(p.paymentInterval);
        OpenView view{*env.current()};
        if (!tryStage(*this, at, [&] { stageLending(env, view, f, s); }))
            return tefINTERNAL;
        return checkLoanSet(env, f, view, p, expected, at);
    }

    // The state the single-value tests ran on (a fresh fixture with the default broker and
    // `cover` deposited): 1% management fee, 10% / 20% cover rates, the vault 30 s into a 1e6 s
    // investment window, or before it, or past it.
    static LendingStage
    singleValueStage(
        ReadView const& view,
        BrokerFixture const& f,
        Number const& cover,
        std::optional<Number> const& debtMaximum,
        bool toInvestment,
        bool toRedemption)
    {
        std::uint32_t const pct = view.parentCloseTime().time_since_epoch().count();
        std::uint32_t sub = pct - 30;
        if (!toInvestment)
            sub = pct + 600;
        if (toRedemption)
            sub = pct - 1'000'001;
        LendingStage s{
            .cover = toUnits(view, f, cover),
            .managementFeeRate = 1'000,
            .coverRate = 10'000,
            .subscriptionDate = sub,
            .redemptionDate = sub + 1'000'000,
        };
        if (debtMaximum)
            s.debtMaximum = toUnits(view, f, *debtMaximum);
        return s;
    }

    // A broker with `cover` of first-loss cover, in the given vault phase, staged on the shared
    // ledger of the asset.
    void
    runLoanSet(
        std::string const& label,
        LoanParams const& p,
        TER expected,
        Number const& cover = Number{500},
        std::optional<Number> const& debtMaximum = std::nullopt,
        bool toInvestment = true,
        bool toRedemption = false,
        LendingAsset assetKind = LendingAsset::iou)
    {
        testcase("LoanSet: " + label + (assetKind == LendingAsset::mpt ? " (MPT)" : ""));
        SweepLedger const& l = ledger(assetKind);
        checkLoanSet(
            *l.env,
            l.f,
            singleValueStage(
                *l.env->current(), l.f, cover, debtMaximum, toInvestment, toRedemption),
            p,
            expected);
    }

    // A two-step proposal on the shared IOU ledger, starting `startOffset` from the parent close
    // time.
    void
    runTwoStep(std::string const& label, std::int64_t startOffset, TER expected)
    {
        testcase("LoanSet: " + label);
        SweepLedger const& l = ledger(LendingAsset::iou);
        std::uint32_t const pct = parentCloseTime(*l.env);
        checkLoanSet(
            *l.env,
            l.f,
            singleValueStage(*l.env->current(), l.f, Number{500}, std::nullopt, true, false),
            LoanParams{.startDate = static_cast<std::uint32_t>(pct + startOffset)},
            expected);
    }

    // LoanAccept of the pending loan at `loanKeylet` on `view` and in the model.
    TER
    checkAccept(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        Keylet const& loanKeylet,
        LoanParams const& p,
        std::optional<TER> expected,
        std::string const& at)
    {
        using namespace jtx;
        Loan const loan = readLoan(view, loanKeylet, f, p);
        Vault const pool = readVaultState(view, f.vaultKeylet, f.asset.raw());
        LawfulTerResult const can =
            leanCanLoanAccept(loan, pool, view.parentCloseTime().time_since_epoch().count());
        expectLawful(can);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS && !can.leanError)
            result = leanLoanAccept(loan, pool);

        zeroIouBalance(view, f.borrower, f.asset.raw());
        Number const borrowerBefore = holding(view, f.borrower, f.asset.raw());
        TER const cppTer = applyOn(env, view, loan::accept(f.borrower, loanKeylet.key));
        TER const lean = leanVerdict(can, result);
        BEAST_EXPECTS(
            lean == cppTer, at + ": cpp=" + transToken(cppTer) + " lean=" + transToken(lean));
        if (expected)
            expectTer(*this, lean, cppTer, *expected);
        if (cppTer != tesSUCCESS || lean != tesSUCCESS)
            return cppTer;
        expectLoanMatches(*this, result->loan, readLoan(view, loanKeylet, f, p));
        expectSameVault(
            *this, "vault ", result->pool, readVaultState(view, f.vaultKeylet, f.asset.raw()));
        // C++ only reads the broker on accept: the model must leave it as it was.
        expectBrokerMatches(*this, result->loan.broker, readBroker(view, f));
        expectNumber(
            *this,
            "amount to borrower",
            result->amountToBorrower,
            holding(view, f.borrower, f.asset.raw()) - borrowerBefore);
        return cppTer;
    }

    // A pending proposal starting `startOffset` seconds from now, accepted after advancing the
    // ledger `acceptAfter` seconds (0 = right away).
    void
    runAccept(std::string const& label, bool pending, std::uint32_t acceptAfter, TER expected)
    {
        using namespace jtx;
        testcase("LoanAccept: " + label);

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams p;
        if (pending)
            p.startDate = parentCloseTime(env) + 1'000;
        auto const loanKeylet = submitLoanSet(env, f, p);
        if (acceptAfter != 0)
            closeAt(env, parentCloseTime(env) + acceptAfter);
        OpenView view{*env.current()};
        checkAccept(env, f, view, loanKeylet, p, expected, label);
    }

    void
    compareDelete(
        jtx::Env& env,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        TER expected)
    {
        using namespace jtx;
        Loan const loan = readLoan(*env.current(), loanKeylet, f, p);
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());

        LawfulTerResult const can = leanCanLoanDelete(loan);
        expectLawful(can);
        std::optional<LeanBrokerPoolResult> result;
        if (can.ter == tesSUCCESS)
            result = leanLoanDelete(loan, pool);

        env(loan::del(f.borrower, loanKeylet.key), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Vault const cppPool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LoanBroker const cppBroker = readBroker(*env.current(), f.brokerKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!can.leanError.has_value(), "lean canDelete error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), "lean delete error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        expectTer(*this, lean, cppTer, expected);
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return;
        BEAST_EXPECT(!env.le(loanKeylet));
        expectSameVault(*this, "vault ", result->pool, cppPool);
        expectBrokerMatches(*this, result->broker, cppBroker);
    }

    // The vault sits at its open limit, so the interest of a new loan does not fit.
    // covered by testOpenZoneSweep
    void
    testLoanInterestPastOpenLimit()
    {
        using namespace jtx;
        testcase("LoanSet: loan interest past the vault's open limit");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{}, Number{kOpenLimitUnits, -6});
        depositCover(env, f, Number{500});
        checkLoanSet(env, f, {}, LoanParams{.interestRate = 10'000}, tecLIMIT_EXCEEDED);
    }

    // Unrealized yield staged just under the open limit: accepting the proposal would add its
    // interest past the limit.
    void
    testAcceptPastOpenLimit()
    {
        using namespace jtx;
        testcase("LoanAccept: interest past the vault's open limit");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams p{.interestRate = 10'000};
        p.startDate = parentCloseTime(env) + 1'000;
        auto const loanKeylet = submitLoanSet(env, f, p);
        Vault const v = readVaultState(env, f.vaultKeylet, f.asset.raw());
        BEAST_EXPECT(updateVaultState(
            env,
            f.vaultKeylet,
            v.assetsTotal,
            v.assetsAvailable,
            static_cast<std::uint64_t>(v.sharesTotal.mantissa()),
            Number{0},
            Number{0},
            Number{kOpenLimitUnits, -6} - v.assetsTotal));
        OpenView view{*env.current()};
        checkAccept(env, f, view, loanKeylet, p, tecLIMIT_EXCEEDED, "past the open limit");
    }

    // Late interest paid on a loan of most of a vault at its open limit pushes the vault's total
    // past 16 digits, coarsening its live scale; a coarsened vault refuses new loans.
    void
    testCoarsenedVaultRefusesLoan()
    {
        using namespace jtx;
        testcase("LoanSet: coarsened vault refuses a loan");

        Env env(*this);
        auto const f = setUpBrokerVault(
            env,
            BrokerConfig{.coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt},
            Number{kOpenLimitUnits, -6},
            false,
            true,
            LendingAsset::iou,
            std::chrono::seconds{10'000'000});
        env(pay(f.issuer, f.borrower, f.asset(Number{2, 10})));
        env.close();
        LoanParams const big{.principal = Number{8, 9}, .lateInterestRate = 100'000};
        auto const loanKeylet = submitLoanSet(env, f, big);
        std::uint32_t const dueDate = env.le(loanKeylet)->at(sfNextPaymentDueDate);
        closeAt(env, dueDate + 4'000'000);
        // The late installment: 4e9 of principal plus about 1.1e9 of late interest.
        env(loan::pay(f.borrower, loanKeylet.key, f.asset(Number{6, 9}), tfLoanLatePayment),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const v = readVaultState(env, f.vaultKeylet, f.asset.raw());
        Number const coarse{1, 10};
        BEAST_EXPECTS(v.assetsTotal >= coarse, "vault total " + to_string(v.assetsTotal));
        checkLoanSet(env, f, {}, LoanParams{}, tecLIMIT_EXCEEDED);
    }

    // The vault phase is judged at the parent close time: a LoanSet exactly at the subscription
    // date is still too soon, exactly at the redemption date already expired.
    // covered by testPhaseSweep
    void
    testLoanSetAtPhaseBoundary(bool atRedemption)
    {
        using namespace jtx;
        testcase(
            std::string("LoanSet: exactly at the ") +
            (atRedemption ? "redemption" : "subscription") + " date");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{}, Number{10'000}, false, false);
        depositCover(env, f, Number{500});
        BEAST_EXPECTS(
            closeExactlyAt(env, atRedemption ? f.redemptionDate : f.subscriptionDate),
            "the parent close time missed the schedule date");
        checkLoanSet(env, f, {}, LoanParams{}, atRedemption ? tecEXPIRED : tecTOO_SOON);
    }

    // A proposal expires at its start date, judged at the parent close time.
    // covered by testAcceptStartDateSweep
    void
    testAcceptAtStartDate()
    {
        using namespace jtx;
        testcase("LoanAccept: exactly at the start date");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        NetClock::time_point const start = alignedTime(
            env, NetClock::time_point{NetClock::duration{parentCloseTime(env) + 1'000}});
        LoanParams p;
        p.startDate = timeCount(start);
        auto const loanKeylet = submitLoanSet(env, f, p);
        BEAST_EXPECTS(closeExactlyAt(env, start), "the parent close time missed the start date");
        OpenView view{*env.current()};
        checkAccept(env, f, view, loanKeylet, p, tecEXPIRED, "at the start date");
    }

    // ---- Sweeps ---------------------------------------------------------------------------------

    void
    testDebtMaximumSweep()
    {
        for (bool const withInterest : {false, true})
        {
            sweepDebtMaximum(ledger(LendingAsset::iou), withInterest);
            sweepDebtMaximum(ledger(LendingAsset::mpt), withInterest);
        }
    }

    // A loan is tecLIMIT_EXCEEDED once the broker's debt plus the principal passes its debt
    // maximum. Rows put debt + principal exactly on the maximum. The debt counts the principal
    // only, so the cusp stays put for the exact-interest loan.
    void
    sweepDebtMaximum(SweepLedger& l, bool withInterest)
    {
        beginCase(("LoanSet " + assetName(l.f) + " debt maximum" +
                   (withInterest ? " with interest" : "") + "-Sweep")
                      .c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kDebtMaximumCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::DebtCusp const& c : cases)
            {
                auto s = investment(*l.env->current());
                s.debt = c.debt;
                s.debtMaximum = c.limit;
                LoanParams p = oneUnitLoan(l, c.principal);
                if (withInterest)
                {
                    p.interestRate = loan_set_sweep::kExactInterestRate;
                    p.paymentInterval = loan_set_sweep::kExactInterestInterval;
                }
                seen.insert(checkLoanSet(*l.env, l.f, s, p));
            }
            expectCrossed(cusp, seen, {tecLIMIT_EXCEEDED});
        }
    }

    void
    testAssetsAvailableSweep()
    {
        sweepAssetsAvailable(ledger(LendingAsset::iou));
        sweepAssetsAvailable(ledger(LendingAsset::mpt));
    }

    // A principal above the vault's available assets is tecINSUFFICIENT_FUNDS. Rows lend out
    // part of the vault first, then exactly the rest.
    void
    sweepAssetsAvailable(SweepLedger& l)
    {
        beginCase(("LoanSet " + assetName(l.f) + " assets available-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kAssetsAvailableCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::DebtCusp const& c : cases)
            {
                auto s = investment(*l.env->current());
                s.debt = c.debt;
                seen.insert(checkLoanSet(*l.env, l.f, s, oneUnitLoan(l, c.principal)));
            }
            expectCrossed(cusp, seen, {tecINSUFFICIENT_FUNDS});
        }
    }

    void
    testOriginationCoverSweep()
    {
        sweepOriginationCover(ledger(LendingAsset::iou));
        sweepOriginationCover(ledger(LendingAsset::mpt));
    }

    // The broker's cover must reach ceil((debt + principal) * rate / 1e5), else
    // tecINSUFFICIENT_FUNDS. Rows deposit exactly that cover.
    void
    sweepOriginationCover(SweepLedger& l)
    {
        beginCase(("LoanSet " + assetName(l.f) + " cover at origination-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kOriginationCoverCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::CoverCusp const& c : cases)
            {
                auto s = investment(*l.env->current());
                s.debt = c.debt;
                s.cover = c.cover;
                s.coverRate = c.rate;
                seen.insert(checkLoanSet(*l.env, l.f, s, oneUnitLoan(l, c.principal)));
            }
            expectCrossed(cusp, seen, {tecINSUFFICIENT_FUNDS});
        }
    }

    void
    testPaymentCountSweep()
    {
        sweepPaymentCount(ledger(LendingAsset::iou));
        sweepPaymentCount(ledger(LendingAsset::mpt));
    }

    // A zero-interest loan with installments 60 s apart is tecPRECISION_LOSS when its rounded-up
    // installment repays it in fewer payments: it passes iff P > (N - 1) * ceil(P / N), in grid
    // units for either asset. Rows sit on a passing P next to a failing one.
    void
    sweepPaymentCount(SweepLedger& l)
    {
        beginCase(("LoanSet " + assetName(l.f) + " payment count-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kPaymentCountCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::PaymentCountCusp const& c : cases)
            {
                LoanParams const p{
                    .principal = units(l.f, c.principal),
                    .paymentInterval = 60,
                    .paymentTotal = static_cast<std::uint32_t>(c.count),
                };
                seen.insert(checkLoanSet(*l.env, l.f, investment(*l.env->current()), p));
            }
            expectCrossed(cusp, seen, {tecPRECISION_LOSS});
        }
    }

    // The last payment of a two-step loan must fall 60 s before the vault's redemption date, else
    // tecNO_PERMISSION. Rows put the redemption date exactly interval * count + 60 after the
    // start (IOU: the principal splits into any number of installments).
    void
    testRedemptionBufferSweep()
    {
        SweepLedger& l = ledger(LendingAsset::iou);
        beginCase(("LoanSet " + assetName(l.f) + " redemption buffer-Sweep").c_str());
        std::uint32_t const pct = parentCloseTime(*l.env);
        std::uint32_t const start = pct + loan_set_sweep::kBufferStart;
        for (auto const& [cusp, cases] : loan_set_sweep::kRedemptionBufferCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::RedemptionBufferCusp const& c : cases)
            {
                LendingStage const s{
                    .subscriptionDate = pct - loan_set_sweep::kBufferStart,
                    .redemptionDate = static_cast<std::uint32_t>(start + c.redemption),
                };
                LoanParams const p{
                    .principal = units(l.f, c.count * loan_set_sweep::kBufferInstallment),
                    .paymentInterval = static_cast<std::uint32_t>(c.interval),
                    .paymentTotal = static_cast<std::uint32_t>(c.count),
                    .startDate = start,
                };
                seen.insert(checkLoanSet(*l.env, l.f, s, p));
            }
            expectCrossed(cusp, seen, {tecNO_PERMISSION});
        }
    }

    void
    testOpenZoneSweep()
    {
        sweepOpenZone(ledger(LendingAsset::iou));
        sweepOpenZone(ledger(LendingAsset::mpt));
    }

    // A loan whose interest would take the vault's assets total + yield past the open limit is
    // tecLIMIT_EXCEEDED. The exact-interest loan owes ceil(P / 10); rows stage the yield so the
    // sum lands exactly on 9e15 units.
    void
    sweepOpenZone(SweepLedger& l)
    {
        beginCase(("LoanSet " + assetName(l.f) + " open zone-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kOpenZoneCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::OpenZoneCusp const& c : cases)
            {
                auto s = investment(*l.env->current());
                s.yield = c.yield;
                LoanParams const p{
                    .principal = units(l.f, c.principal),
                    .interestRate = loan_set_sweep::kExactInterestRate,
                    .paymentInterval = loan_set_sweep::kExactInterestInterval,
                    .paymentTotal = 1,
                };
                seen.insert(checkLoanSet(*l.env, l.f, s, p));
            }
            expectCrossed(cusp, seen, {tecLIMIT_EXCEEDED});
        }
    }

    // C++ preflight refuses an origination fee above the principal (temINVALID). Rows put the
    // fee exactly on the principal.
    void
    testOriginationFeeSweep()
    {
        sweepOriginationFee(ledger(LendingAsset::iou));
        sweepOriginationFee(ledger(LendingAsset::mpt));
    }

    void
    sweepOriginationFee(SweepLedger& l)
    {
        beginCase(("LoanSet " + assetName(l.f) + " origination fee-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kOriginationFeeCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::OriginationFeeCusp const& c : cases)
            {
                LoanParams p = oneUnitLoan(l, c.principal);
                p.originationFee = units(l.f, c.fee);
                seen.insert(checkLoanSet(*l.env, l.f, investment(*l.env->current()), p));
            }
            expectCrossed(cusp, seen, {temINVALID});
        }
    }

    // The LoanSet value fields, each checked against the vault grid and the asset's range.
    static constexpr Number LoanParams::* kValueFields[] = {
        &LoanParams::principal,
        &LoanParams::originationFee,
        &LoanParams::serviceFee,
        &LoanParams::latePaymentFee,
        &LoanParams::closePaymentFee,
    };

    static std::string
    fieldName(Number LoanParams::* field)
    {
        if (field == &LoanParams::principal)
            return "principal";
        if (field == &LoanParams::originationFee)
            return "origination fee";
        if (field == &LoanParams::serviceFee)
            return "service fee";
        if (field == &LoanParams::latePaymentFee)
            return "late fee";
        return "close fee";
    }

    void
    testGridSweep()
    {
        sweepGrid(ledger(LendingAsset::iou));
        sweepGrid(ledger(LendingAsset::mpt));
    }

    // A value field off the vault grid is tecPRECISION_LOSS (for an MPT, a fractional amount). A
    // moved one-step mantissa leaves the grid. Fees ride on a 2e9-unit loan, above any fee level.
    void
    sweepGrid(SweepLedger& l)
    {
        for (Number LoanParams::* field : kValueFields)
        {
            for (int const level : loan_set_sweep::kGridLevels)
            {
                beginCase(("LoanSet " + assetName(l.f) + " " + fieldName(field) + " grid at 1e" +
                           std::to_string(level) + "-Sweep")
                              .c_str());
                for (auto const& [cusp, cases] : loan_set_sweep::kOneStepCases)
                {
                    std::set<TER> seen;
                    for (std::int64_t const mantissa : cases)
                    {
                        LoanParams p = oneUnitLoan(l, 2 * loan_set_sweep::kOrdinaryUnits);
                        p.*field = gridStep(*l.env->current(), l.f, mantissa, level);
                        seen.insert(checkLoanSet(*l.env, l.f, investment(*l.env->current()), p));
                    }
                    expectCrossed(cusp, seen, {tecPRECISION_LOSS});
                }
            }
        }
    }

    // A value field above the MPT maximum 2^63 - 1 is tecPRECISION_LOSS. The row is the largest
    // 16-digit mantissa at exponent 3 under the cap. The origination fee is bounded by the
    // principal, so it never reaches the cap alone.
    void
    testMptCapSweep()
    {
        SweepLedger& l = ledger(LendingAsset::mpt);
        for (Number LoanParams::* field : kValueFields)
        {
            if (field == &LoanParams::originationFee)
                continue;
            beginCase(
                ("LoanSet " + assetName(l.f) + " " + fieldName(field) + " cap-Sweep").c_str());
            for (auto const& [cusp, cases] : loan_set_sweep::kDebtCapCases)
            {
                std::set<TER> seen;
                for (std::int64_t const mantissa : cases)
                {
                    LoanParams p = oneUnitLoan(l, loan_set_sweep::kOrdinaryUnits);
                    p.*field = Number{mantissa, 3};
                    seen.insert(checkLoanSet(*l.env, l.f, investment(*l.env->current()), p));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    // A negative service, late or close fee is temINVALID; zero is the minimum.
    void
    testFeeMinimumSweep()
    {
        for (LendingAsset const kind : {LendingAsset::iou, LendingAsset::mpt})
        {
            SweepLedger& l = ledger(kind);
            for (Number LoanParams::* field : kValueFields)
            {
                if (field == &LoanParams::principal || field == &LoanParams::originationFee)
                    continue;
                beginCase(("LoanSet " + assetName(l.f) + " " + fieldName(field) + " minimum-Sweep")
                              .c_str());
                for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
                {
                    std::set<TER> seen;
                    for (std::int64_t const fee : cases)
                    {
                        LoanParams p = oneUnitLoan(l, loan_set_sweep::kOrdinaryUnits);
                        p.*field = units(l.f, fee);
                        seen.insert(checkLoanSet(*l.env, l.f, investment(*l.env->current()), p));
                    }
                    expectCrossed(cusp, seen, {temINVALID});
                }
            }
        }
    }

    // A schedule whose last grace period ends past 2^32 - 1 is tecKILLED, checked first. Rows end
    // it exactly there; below it the proposal fails the redemption buffer (no investment window
    // reaches 2^32 - 1) or, starting at 0, has expired.
    void
    testTimeLimitSweep()
    {
        SweepLedger& l = ledger(LendingAsset::iou);
        beginCase(("LoanSet " + assetName(l.f) + " protocol time limit-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kTimeLimitCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::TimeLimitCusp const& c : cases)
            {
                LoanParams const p{
                    .principal = units(l.f, loan_set_sweep::kTimeLimitPrincipal),
                    .paymentInterval = static_cast<std::uint32_t>(c.interval),
                    .paymentTotal = static_cast<std::uint32_t>(c.total),
                    .gracePeriod = static_cast<std::uint32_t>(c.grace),
                    .startDate = static_cast<std::uint32_t>(c.start),
                };
                seen.insert(checkLoanSet(*l.env, l.f, investment(*l.env->current()), p));
            }
            expectCrossed(cusp, seen, {tecKILLED});
        }
    }

    // A LoanSet at or before the subscription date is tecTOO_SOON; at or after the redemption date
    // tecEXPIRED (just before it, the schedule no longer fits: tecNO_PERMISSION).
    void
    testPhaseSweep()
    {
        SweepLedger& l = ledger(LendingAsset::iou);
        beginCase(("LoanSet " + assetName(l.f) + " phase dates-Sweep").c_str());
        std::uint32_t const pct = parentCloseTime(*l.env);
        for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
        {
            std::set<TER> seen;
            for (std::int64_t const d : cases)
            {
                LendingStage const s{
                    .subscriptionDate = static_cast<std::uint32_t>(pct + d),
                    .redemptionDate = pct + 900'000'000,
                };
                seen.insert(checkLoanSet(*l.env, l.f, s, oneUnitLoan(l, 1'000)));
            }
            expectCrossed(cusp, seen, {tecTOO_SOON});
        }
        for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
        {
            std::set<TER> seen;
            for (std::int64_t const d : cases)
            {
                LendingStage const s{
                    .subscriptionDate = static_cast<std::uint32_t>(pct + d - 1'000'000),
                    .redemptionDate = static_cast<std::uint32_t>(pct + d),
                };
                seen.insert(checkLoanSet(*l.env, l.f, s, oneUnitLoan(l, 1'000)));
            }
            expectCrossed(cusp, seen, {tecEXPIRED});
        }
    }

    // A two-step proposal starting at or before the parent close time is tecEXPIRED.
    // Covers "two-step proposal starting at the parent close time" and "... one second after".
    void
    testStartDateSweep()
    {
        SweepLedger& l = ledger(LendingAsset::iou);
        beginCase(("LoanSet " + assetName(l.f) + " start date-Sweep").c_str());
        std::uint32_t const pct = parentCloseTime(*l.env);
        for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
        {
            std::set<TER> seen;
            for (std::int64_t const d : cases)
            {
                LoanParams p = oneUnitLoan(l, 1'000);
                p.startDate = static_cast<std::uint32_t>(pct + d);
                seen.insert(checkLoanSet(*l.env, l.f, investment(*l.env->current()), p));
            }
            expectCrossed(cusp, seen, {tecEXPIRED});
        }
    }

    // Accepting a proposal whose start date is at or before the parent close time is tecEXPIRED;
    // a vault at or past its redemption date is tecEXPIRED too (LoanAccept does not re-check the
    // redemption buffer). Rows stage the proposal's start date, then the redemption date.
    void
    testAcceptSweep()
    {
        SweepLedger& l = ledger(LendingAsset::iou);
        beginCase(("LoanAccept " + assetName(l.f) + " start date-Sweep").c_str());
        std::uint32_t const pct = parentCloseTime(*l.env);
        for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
        {
            std::set<TER> seen;
            for (std::int64_t const d : cases)
            {
                seen.insert(checkStagedAccept(
                    l,
                    oneUnitLoan(l, 1'000),
                    {},
                    static_cast<std::uint32_t>(pct + d),
                    std::nullopt,
                    "start P + " + std::to_string(d)));
            }
            expectCrossed(cusp, seen, {tecEXPIRED});
        }
        beginCase(("LoanAccept " + assetName(l.f) + " redemption date-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
        {
            std::set<TER> seen;
            for (std::int64_t const d : cases)
            {
                seen.insert(checkStagedAccept(
                    l,
                    oneUnitLoan(l, 1'000),
                    {},
                    std::nullopt,
                    static_cast<std::uint32_t>(pct + d),
                    "redemption P + " + std::to_string(d)));
            }
            expectCrossed(cusp, seen, {tecEXPIRED});
        }
    }

    void
    testAcceptOpenZoneSweep()
    {
        sweepAcceptOpenZone(ledger(LendingAsset::iou));
        sweepAcceptOpenZone(ledger(LendingAsset::mpt));
    }

    // Accepting a proposal whose interest would take the vault past the open limit is
    // tecLIMIT_EXCEEDED. The open zone rows of LoanSet, with the yield staged after the proposal.
    void
    sweepAcceptOpenZone(SweepLedger& l)
    {
        beginCase(("LoanAccept " + assetName(l.f) + " open zone-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kOpenZoneCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::OpenZoneCusp const& c : cases)
            {
                LoanParams const p{
                    .principal = units(l.f, c.principal),
                    .interestRate = loan_set_sweep::kExactInterestRate,
                    .paymentInterval = loan_set_sweep::kExactInterestInterval,
                    .paymentTotal = 1,
                };
                seen.insert(checkStagedAccept(
                    l,
                    p,
                    {.yield = c.yield},
                    std::nullopt,
                    std::nullopt,
                    loan_set_sweep::describe(c)));
            }
            expectCrossed(cusp, seen, {tecLIMIT_EXCEEDED});
        }
    }

    // A two-step proposal of `p` created on a throwaway view, then `after` staged (with its start
    // date or the vault's redemption date restaged) before the borrower accepts.
    TER
    checkStagedAccept(
        SweepLedger& l,
        LoanParams p,
        LendingStage const& after,
        std::optional<std::uint32_t> startDate,
        std::optional<std::uint32_t> redemptionDate,
        std::string const& at)
    {
        jtx::Env& env = *l.env;
        OpenView view{*env.current()};
        p.startDate = parentCloseTime(env) + loan_set_sweep::kBufferStart;
        Keylet const loanKeylet = nextLoan(view, l.f);
        if (!tryStage(*this, at, [&] {
                stageLending(env, view, l.f, investment(view));
                TER const proposed = applyLoanSet(env, view, l.f, p);
                if (proposed != tesSUCCESS)
                    throw std::runtime_error("proposal " + transToken(proposed));
                stageLending(env, view, l.f, after);
            }))
            return tefINTERNAL;
        Sandbox sb(&view, TapNone);
        if (startDate)
        {
            auto const loan = sb.peek(loanKeylet);
            loan->at(sfStartDate) = *startDate;
            sb.update(loan);
        }
        if (redemptionDate)
        {
            auto const vault = sb.peek(l.f.vaultKeylet);
            vault->at(sfSubscriptionDate) = *redemptionDate - 1'000'000;
            vault->at(sfRedemptionDate) = *redemptionDate;
            sb.update(vault);
        }
        sb.apply(view);
        return checkAccept(env, l.f, view, loanKeylet, p, std::nullopt, at);
    }

    // A zero-interest one-payment loan of `principal` units.
    static LoanParams
    oneUnitLoan(SweepLedger& l, std::int64_t principal)
    {
        return LoanParams{.principal = units(l.f, principal), .paymentTotal = 1};
    }

    void
    runDelete(std::string const& label, LoanKind kind, TER expected, bool withOtherLoan = false)
    {
        using namespace jtx;
        testcase("LoanDelete: " + label);

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        if (withOtherLoan)
            issueLoan(env, f, Number{1'000});
        LoanParams p;
        if (kind == LoanKind::pending)
            p.startDate = parentCloseTime(env) + 1'000;
        if (kind == LoanKind::paidOff)
            p.paymentTotal = 1;
        auto const loanKeylet = submitLoanSet(env, f, p);
        if (kind == LoanKind::paidOff)
        {
            env(loan::pay(f.borrower, loanKeylet.key, f.asset(1'000)), jtx::Ter(tesSUCCESS));
            env.close();
        }
        compareDelete(env, f, loanKeylet, p, expected);
    }

    void
    runTests() override
    {
        jtx::Env iouEnv(*this);
        iou_ = SweepLedger{
            .env = &iouEnv,
            .f = setUpSweepBroker(iouEnv, LendingAsset::iou, loan_set_sweep::kSeedUnits),
        };
        jtx::Env mptEnv(*this);
        mpt_ = SweepLedger{
            .env = &mptEnv,
            .f = setUpSweepBroker(mptEnv, LendingAsset::mpt, loan_set_sweep::kSeedUnits),
        };

        // One-step loans
        runLoanSet("one-step loan without interest", LoanParams{}, tesSUCCESS);
        runLoanSet(
            "one-step loan with interest",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            tesSUCCESS);
        runLoanSet(
            "one-step loan with fees",
            LoanParams{
                .interestRate = 10'000,
                .originationFee = Number{5},
                .serviceFee = Number{1},
                .latePaymentFee = Number{2},
                .closePaymentFee = Number{3}},
            tesSUCCESS);
        runLoanSet(
            "vault in the subscription phase",
            LoanParams{},
            tecTOO_SOON,
            Number{500},
            std::nullopt,
            false);
        runLoanSet(
            "vault in the redemption phase",
            LoanParams{},
            tecEXPIRED,
            Number{500},
            std::nullopt,
            true,
            true);
        // covered by testRedemptionBufferSweep
        runLoanSet(
            "final payment too close to the redemption date",
            LoanParams{.paymentInterval = 500'000},
            tecNO_PERMISSION);
        // covered by testAssetsAvailableSweep
        runLoanSet(
            "principal above the vault's available assets",
            LoanParams{.principal = Number{20'000}},
            tecINSUFFICIENT_FUNDS,
            Number{5'000});
        // covered by testDebtMaximumSweep
        runLoanSet(
            "principal above the debt maximum",
            LoanParams{},
            tecLIMIT_EXCEEDED,
            Number{500},
            Number{500});
        // covered by testOriginationCoverSweep
        runLoanSet("not enough cover", LoanParams{}, tecINSUFFICIENT_FUNDS, Number{0});
        runLoanSet(
            "fee off the vault grid",
            LoanParams{.originationFee = Number{1, -7}},
            tecPRECISION_LOSS);
        // One grid unit in three installments: the rounded-up installment covers the whole loan in
        // one payment, so the schedule cannot be honoured.
        // covered by testPaymentCountSweep
        runLoanSet(
            "principal too small for its installments",
            LoanParams{.principal = Number{1, -6}, .paymentTotal = 3},
            tecPRECISION_LOSS);
        runLoanSet(
            "schedule past the protocol time limit",
            LoanParams{.paymentInterval = 4'000'000'000},
            tecKILLED);
        runLoanSet(
            "grace period past the protocol time limit",
            LoanParams{.paymentInterval = 0xFFFF'FFFF, .gracePeriod = 0xFFFF'FFFF},
            tecKILLED);
        runLoanSet(
            "interval past the protocol time limit",
            LoanParams{.paymentInterval = 0xFFFF'FFFF},
            tecKILLED);
        runLoanSet(
            "installment count past the protocol time limit",
            LoanParams{.paymentTotal = 0xFFFF'FFFF},
            tecKILLED);
        runLoanSet(
            "fee not representable as an amount",
            LoanParams{.originationFee = Number{12'345'678'901'234'567LL, -16}},
            tecPRECISION_LOSS);
        // A per-period rate below 1e-9 takes the binomial series.
        runLoanSet(
            "tiny interest rate",
            LoanParams{.principal = Number{5'000}, .interestRate = 10, .paymentInterval = 60},
            tesSUCCESS);
        // A tiny rate over many installments (rate times count still below 1e-9): the binomial
        // series converges before its last term.
        runLoanSet(
            "tiny interest rate over 50 installments",
            LoanParams{
                .principal = Number{5'000},
                .interestRate = 1,
                .paymentInterval = 60,
                .paymentTotal = 50},
            tesSUCCESS);
        testLoanInterestPastOpenLimit();
        testAcceptPastOpenLimit();
        testCoarsenedVaultRefusesLoan();

        // MPT vault
        runLoanSet(
            "one-step loan with interest",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            tesSUCCESS,
            Number{500},
            std::nullopt,
            true,
            false,
            LendingAsset::mpt);
        runLoanSet(
            "one-step loan with fees",
            LoanParams{
                .interestRate = 10'000,
                .originationFee = Number{5},
                .serviceFee = Number{1},
                .latePaymentFee = Number{2},
                .closePaymentFee = Number{3}},
            tesSUCCESS,
            Number{500},
            std::nullopt,
            true,
            false,
            LendingAsset::mpt);
        runLoanSet(
            "fee off the vault grid",
            LoanParams{.originationFee = Number{5, -1}},
            tecPRECISION_LOSS,
            Number{500},
            std::nullopt,
            true,
            false,
            LendingAsset::mpt);
        runLoanSet(
            "principal above the MPT maximum",
            LoanParams{.principal = Number{1, 19}},
            tecPRECISION_LOSS,
            Number{500},
            std::nullopt,
            true,
            false,
            LendingAsset::mpt);

        // Two-step proposals
        runTwoStep("two-step proposal", 1'000, tesSUCCESS);
        runTwoStep("two-step proposal with an expired start date", -10, tecEXPIRED);
        // Start dates are judged at the parent close time, not the ledger close time.
        // covered by testStartDateSweep
        runTwoStep("two-step proposal starting at the parent close time", 0, tecEXPIRED);
        runTwoStep(
            "two-step proposal starting one second after the parent close time", 1, tesSUCCESS);
        testLoanSetAtPhaseBoundary(false);
        testLoanSetAtPhaseBoundary(true);

        // LoanAccept
        runAccept("accept a pending proposal", true, 0, tesSUCCESS);
        testAcceptAtStartDate();
        runAccept("accept after the start date", true, 2'000, tecEXPIRED);
        runAccept("accept an active loan", false, 0, tecNO_PERMISSION);

        // LoanDelete
        runDelete("delete an active loan", LoanKind::active, tecHAS_OBLIGATIONS);
        runDelete("delete a pending proposal", LoanKind::pending, tesSUCCESS);
        runDelete("delete a paid-off loan", LoanKind::paidOff, tesSUCCESS);
        // The broker keeps its debt when another loan remains.
        runDelete(
            "delete a pending proposal beside an active loan", LoanKind::pending, tesSUCCESS, true);

        // Sweeps
        testDebtMaximumSweep();
        testAssetsAvailableSweep();
        testOriginationCoverSweep();
        testPaymentCountSweep();
        testRedemptionBufferSweep();
        testOpenZoneSweep();
        testGridSweep();
        testPhaseSweep();
        testStartDateSweep();
        testAcceptSweep();
        testOriginationFeeSweep();
        testMptCapSweep();
        testFeeMinimumSweep();
        testTimeLimitSweep();
        testAcceptOpenZoneSweep();
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanSet, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
