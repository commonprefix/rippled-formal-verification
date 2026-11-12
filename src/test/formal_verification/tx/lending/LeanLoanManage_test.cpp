#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/formal_verification/tx/lending/LoanPaySweepCases.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

using namespace loan_pay_sweep;

// Differential tests of LoanManage: impair, unimpair and default.
class LeanLoanManage_test : public LeanSuite
{
    static std::uint32_t
    flagsOf(ManageAction action)
    {
        switch (action)
        {
            case ManageAction::impair:
                return tfLoanImpair;
            case ManageAction::unimpair:
                return tfLoanUnimpair;
            case ManageAction::defaultLoan:
                return tfLoanDefault;
        }
        return 0;
    }

    static std::string
    actionName(ManageAction action)
    {
        switch (action)
        {
            case ManageAction::impair:
                return "impair";
            case ManageAction::unimpair:
                return "unimpair";
            case ManageAction::defaultLoan:
                return "default";
        }
        return "?";
    }

    // One LoanManage on `view`: C++ applies it there, the model runs on the same pre-state. The
    // verdicts must agree and, on success, so must the post-states. Returns the C++ verdict.
    TER
    checkManage(
        jtx::Env& env,
        OpenView& view,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        ManageAction action,
        std::string const& at = {})
    {
        using namespace jtx;
        Asset const asset = f.asset.raw();
        Loan const loan = readLoan(view, loanKeylet, f, p);
        Vault const pool = readVaultState(view, f.vaultKeylet, asset);
        std::uint32_t const now = parentCloseTime(env);

        LawfulTerResult const can = leanCanLoanManage(loan, action, now);
        expectLawful(can);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS && !can.leanError)
            result = leanLoanManage(loan, pool, action, now);

        TER const cppTer =
            applyOn(env, view, loan::manage(f.owner, loanKeylet.key, flagsOf(action)));

        BEAST_EXPECTS(!can.leanError.has_value(), at + "lean canManage error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), at + "lean manage error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        BEAST_EXPECTS(
            lean == cppTer, at + "cpp=" + transToken(cppTer) + " lean=" + transToken(lean));
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return cppTer;

        Loan const cppLoan = readLoan(view, loanKeylet, f, p);
        Vault const cppPool = readVaultState(view, f.vaultKeylet, asset);
        expectLoanMatches(*this, result->loan, cppLoan);
        expectSameVault(*this, "vault ", result->pool, cppPool);
        expectBrokerMatches(*this, result->loan.broker, cppLoan.broker);
        // A default moves the cover it consumes into the vault.
        expectNumber(
            *this,
            "amount to pool",
            result->amountToPool,
            cppPool.assetsAvailable - pool.assetsAvailable);
        return cppTer;
    }

    // A 1000 loan (two installments 600 s apart, 60 s grace) on a throwaway view of the fixture,
    // started `delay` seconds before the parent close time, and impaired first if `impairFirst`
    // (which needs the loan to be late).
    void
    runManage(
        jtx::Env& env,
        BrokerFixture const& f,
        std::string const& label,
        std::uint32_t delay,
        bool impairFirst,
        ManageAction action,
        TER expected,
        LoanKind kind = LoanKind::active)
    {
        using namespace jtx;
        testcase(actionName(action) + ": " + label);

        OpenView view{*env.current()};
        LoanParams p;
        std::optional<Keylet> staged;
        if (!tryStage(*this, label, [&] {
                staged = stageLoan(env, view, f, p, kind, parentCloseTime(env), delay);
            }))
            return;
        Keylet const loanKeylet = *staged;
        if (impairFirst)
        {
            BEAST_EXPECT(
                applyOn(env, view, loan::manage(f.owner, loanKeylet.key, tfLoanImpair)) ==
                tesSUCCESS);
        }
        if (kind == LoanKind::defaulted)
        {
            BEAST_EXPECT(
                applyOn(env, view, loan::manage(f.owner, loanKeylet.key, tfLoanDefault)) ==
                tesSUCCESS);
        }
        TER const cpp = checkManage(env, view, f, loanKeylet, p, action);
        BEAST_EXPECTS(
            cpp == expected,
            std::string("cpp=") + transToken(cpp) + " expected " + transToken(expected));
    }

    // ---- Sweeps ----

    using SweepFixtures = std::vector<SweepLedger>;

    // No cover rates, kSweepSeed units in the vault, an investment window long enough for 30-day
    // intervals, and a clock far enough from zero for due dates staged a month back.
    static BrokerFixture
    sweepFixture(jtx::Env& env, LendingAsset kind)
    {
        Number const seed = kind == LendingAsset::mpt ? Number{kSweepSeed} : Number{kSweepSeed, -6};
        auto const f = setUpBrokerVault(
            env,
            BrokerConfig{.coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt},
            seed,
            false,
            true,
            kind,
            std::chrono::seconds{200'000'000});
        env.close(env.now() + std::chrono::seconds{10'000'000});
        return f;
    }

    // A default needs the parent close time past due date + grace period (exclusive), else
    // tecTOO_SOON. Rows put that deadline exactly on the parent close time.
    void
    testDefaultSweep(SweepFixtures const& fixtures)
    {
        for (auto const& [envPtr, f] : fixtures)
        {
            jtx::Env& env = *envPtr;
            beginCase(("LoanManage " + assetName(f) + " default deadline-Sweep").c_str());
            std::uint32_t const now = parentCloseTime(env);
            for (auto const& [cusp, cases] : kDefaultCases)
            {
                std::set<TER> seen;
                for (DefaultCusp const& c : cases)
                {
                    OpenView view{*env.current()};
                    LoanParams const p{
                        .paymentInterval = c.interval,
                        .gracePeriod = static_cast<std::uint32_t>(c.grace),
                    };
                    auto const loan = createLoan(env, view, f, p);
                    dueAt(view, loan, now, c.dueOffset - c.cuspGrace);
                    seen.insert(checkManage(
                        env, view, f, loan, p, ManageAction::defaultLoan, describe(c) + ": "));
                }
                expectCrossed(cusp, seen, {tecTOO_SOON});
            }
        }
    }

    void
    testImpairSweep(SweepFixtures const& fixtures)
    {
        for (auto const& [envPtr, f] : fixtures)
        {
            jtx::Env& env = *envPtr;
            sweepImpairDue(env, f);
            sweepLossCap(env, f);
        }
    }

    // An impairment needs the parent close time past the due date (exclusive), else tecTOO_SOON.
    void
    sweepImpairDue(jtx::Env& env, BrokerFixture const& f)
    {
        beginCase(("LoanManage " + assetName(f) + " impair due date-Sweep").c_str());
        std::uint32_t const now = parentCloseTime(env);
        // The due date staged at now + offset.
        for (auto const& [cusp, cases] : kZeroCases)
        {
            std::set<TER> seen;
            for (std::int64_t const dueOffset : cases)
            {
                OpenView view{*env.current()};
                LoanParams const p;
                auto const loan = createLoan(env, view, f, p);
                dueAt(view, loan, now, dueOffset);
                seen.insert(checkManage(
                    env, view, f, loan, p, ManageAction::impair, describe(dueOffset) + ": "));
            }
            expectCrossed(cusp, seen, {tecTOO_SOON});
        }
    }

    // An impairment adds the loan's principal to the unrealized loss; past the deployed assets it
    // is tecLIMIT_EXCEEDED. The vault's deployed assets and loss are staged after the loan.
    void
    sweepLossCap(jtx::Env& env, BrokerFixture const& f)
    {
        beginCase(("LoanManage " + assetName(f) + " impair loss cap-Sweep").c_str());
        std::uint32_t const now = parentCloseTime(env);
        for (auto const& [cusp, cases] : kLossCapCases)
        {
            std::set<TER> seen;
            for (LossCapCusp const& c : cases)
            {
                OpenView view{*env.current()};
                LoanParams const p{.principal = units(f, c.principal), .paymentTotal = 1};
                auto const loan = createLoan(env, view, f, p);
                dueAt(view, loan, now, -1);
                stageDeployed(view, f.vaultKeylet, units(f, c.deployed), units(f, c.loss));
                seen.insert(
                    checkManage(env, view, f, loan, p, ManageAction::impair, describe(c) + ": "));
            }
            expectCrossed(cusp, seen, {tecLIMIT_EXCEEDED});
        }
    }

    void
    testDefaultCoverSweep(SweepFixtures const& fixtures)
    {
        for (auto const& [envPtr, f] : fixtures)
        {
            jtx::Env& env = *envPtr;
            beginCase(
                ("LoanManage " + assetName(f) + " default cover at the principal-Sweep").c_str());
            for (auto const& [cusp, cases] : kDefaultPrincipalCases)
            {
                for (DefaultCoverCusp const& c : cases)
                {
                    checkDefaultCover(env, f, c);
                }
            }
            beginCase(("LoanManage " + assetName(f) + " default cover at the cover available-Sweep")
                          .c_str());
            for (auto const& [cusp, cases] : kDefaultAvailableCases)
            {
                for (DefaultCoverCusp const& c : cases)
                {
                    checkDefaultCover(env, f, c);
                }
            }
        }
    }

    // A default of a `principal` loan beside a `debt` loan, with `cover` deposited and the
    // minimum cover rate set after both loans. The cover moved into the vault is
    // min(min(minimum cover * 20%, principal), cover); the verdict does not change.
    TER
    checkDefaultCover(jtx::Env& env, BrokerFixture const& f, DefaultCoverCusp const& c)
    {
        std::string const at = describe(c) + ": ";
        OpenView view{*env.current()};
        LoanParams const p{.principal = units(f, c.principal)};
        std::optional<Keylet> loan;
        if (!tryStage(*this, at, [&] {
                stageLending(env, view, f, {.debt = c.debt});
                loan = createLoan(env, view, f, p);
                stageLending(env, view, f, {.cover = c.cover, .coverRate = c.rate});
                dueAt(view, *loan, parentCloseTime(env), -61);
            }))
            return tefINTERNAL;
        return checkManage(env, view, f, *loan, p, ManageAction::defaultLoan, at);
    }

    void
    runTests() override
    {
        // The single-value tests share one fixture per configuration (broker cover 500); each
        // test runs on a throwaway view of it.
        jtx::Env env(*this);
        auto const iou = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, iou, Number{500});
        jtx::Env mptEnv(*this);
        auto const mpt = setUpBrokerVault(
            mptEnv, BrokerConfig{}, Number{10'000}, false, true, LendingAsset::mpt);
        depositCover(mptEnv, mpt, Number{500});
        // Loans are aged by moving their dates back; keep those dates well above zero.
        env.close(env.now() + std::chrono::seconds{10'000});
        mptEnv.close(mptEnv.now() + std::chrono::seconds{10'000});
        // No cover rates and no cover: also the IOU sweep fixture.
        jtx::Env iouSweepEnv(*this);
        auto const iouSweep = sweepFixture(iouSweepEnv, LendingAsset::iou);
        jtx::Env mptSweepEnv(*this);
        auto const mptSweep = sweepFixture(mptSweepEnv, LendingAsset::mpt);

        // The first installment is due 600 s after the start, with a 60 s grace period.
        runManage(env, iou, "a late loan", 601, false, ManageAction::impair, tesSUCCESS);
        // covered by testImpairSweep
        runManage(env, iou, "a loan that is not late", 0, false, ManageAction::impair, tecTOO_SOON);
        runManage(env, iou, "an impaired loan", 601, true, ManageAction::impair, tecNO_PERMISSION);

        runManage(env, iou, "an impaired loan", 601, true, ManageAction::unimpair, tesSUCCESS);
        runManage(
            env,
            iou,
            "a loan that is not impaired",
            0,
            false,
            ManageAction::unimpair,
            tecNO_PERMISSION);

        // covered by testDefaultSweep
        runManage(
            env,
            iou,
            "before the grace period ends",
            601,
            false,
            ManageAction::defaultLoan,
            tecTOO_SOON);
        runManage(
            env, iou, "after the grace period", 700, false, ManageAction::defaultLoan, tesSUCCESS);
        runManage(
            env,
            iou,
            "an impaired loan after the grace period",
            700,
            true,
            ManageAction::defaultLoan,
            tesSUCCESS);

        runManage(
            mptEnv,
            mpt,
            "an MPT loan after the grace period",
            700,
            false,
            ManageAction::defaultLoan,
            tesSUCCESS);
        runManage(
            mptEnv,
            mpt,
            "an impaired MPT loan after the grace period",
            700,
            true,
            ManageAction::defaultLoan,
            tesSUCCESS);
        runManage(
            iouSweepEnv,
            iouSweep,
            "a broker without cover",
            700,
            false,
            ManageAction::defaultLoan,
            tesSUCCESS);

        // Loans that cannot be managed at all
        runManage(
            env,
            iou,
            "a pending proposal",
            0,
            false,
            ManageAction::impair,
            tecNO_PERMISSION,
            LoanKind::pending);
        runManage(
            env,
            iou,
            "a defaulted loan",
            700,
            false,
            ManageAction::impair,
            tecNO_PERMISSION,
            LoanKind::defaulted);
        runManage(
            env,
            iou,
            "a paid-off loan",
            0,
            false,
            ManageAction::impair,
            tecNO_PERMISSION,
            LoanKind::paidOff);

        SweepFixtures const fixtures{
            {.env = &iouSweepEnv, .f = iouSweep},
            {.env = &mptSweepEnv, .f = mptSweep},
        };
        testDefaultSweep(fixtures);
        testImpairSweep(fixtures);
        testDefaultCoverSweep(fixtures);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanManage, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
