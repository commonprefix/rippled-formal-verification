#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

// Differential tests of LoanSet (one-step and two-step), LoanAccept and LoanDelete. Each case
// compares the model's preclaim TER, then (when preclaim accepts) its doApply TER and the loan,
// vault and broker post-states.
class LeanLoanSet_test : public LeanSuite
{
    void
    expectTer(TER lean, TER cpp, TER expected)
    {
        BEAST_EXPECTS(
            cpp == expected,
            std::string("cpp=") + transToken(cpp) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            lean == expected,
            std::string("lean=") + transToken(lean) + " expected " + transToken(expected));
    }

    void
    compareLoanSet(jtx::Env& env, BrokerFixture const& f, LoanParams const& p, TER expected)
    {
        using namespace jtx;
        LoanBroker const broker = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LoanSetArgs const args = loanSetArgs(p);
        std::uint32_t const closeTime = ledgerCloseTime(env);
        bool const twoStep = p.startDate.has_value();

        LawfulTerResult const can =
            leanCanLoanCreate(broker, pool, args, closeTime, parentCloseTime(env));
        expectLawful(can);
        Loan const like = loanTemplate(broker, p, twoStep ? *p.startDate : closeTime);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS)
            result = leanLoanCreate(broker, pool, args, closeTime, like);

        auto const loanKeylet = nextLoanKeylet(env, f);
        auto const tx = loanSetTx(f, p);
        if (twoStep)
            env(tx, jtx::Ter(std::ignore));
        else
            env(tx,
                Sig(sfCounterpartySignature, f.owner),
                Fee(env.current()->fees().base * 2),
                jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        std::optional<Loan> cppLoan;
        if (cppTer == tesSUCCESS)
            cppLoan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const cppPool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LoanBroker const cppBroker = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!can.leanError.has_value(), "lean canCreate error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), "lean create error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        expectTer(lean, cppTer, expected);
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return;

        expectLoanMatches(*this, result->loan, *cppLoan);
        expectVaultMatches(*this, result->pool, cppPool);
        expectBrokerMatches(*this, result->loan.broker, cppBroker);
    }

    // A broker with `cover` of first-loss cover, in the given vault phase.
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
        using namespace jtx;
        using namespace std::chrono_literals;
        testcase("LoanSet: " + label + (assetKind == LendingAsset::mpt ? " (MPT)" : ""));

        Env env(*this);
        auto const f = setUpBrokerVault(
            env,
            BrokerConfig{.debtMaximum = debtMaximum},
            Number{10'000},
            false,
            toInvestment,
            assetKind);
        if (cover != Number{0})
            depositCover(env, f, cover);
        if (toRedemption)
            env.close(f.subscriptionDate + kBrokerInvestmentWindow + 1s);
        compareLoanSet(env, f, p, expected);
    }

    void
    compareAccept(
        jtx::Env& env,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        TER expected)
    {
        using namespace jtx;
        Loan const loan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        std::uint32_t const now = parentCloseTime(env);

        LawfulTerResult const can = leanCanLoanAccept(loan, pool, now);
        expectLawful(can);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS)
            result = leanLoanAccept(loan, pool);

        env(loan::accept(f.borrower, loanKeylet.key), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Loan const cppLoan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const cppPool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!can.leanError.has_value(), "lean canAccept error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), "lean accept error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        expectTer(lean, cppTer, expected);
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return;
        expectLoanMatches(*this, result->loan, cppLoan);
        expectVaultMatches(*this, result->pool, cppPool);
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
        compareAccept(env, f, loanKeylet, p, expected);
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
        Loan const loan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());

        LawfulTerResult const can = leanCanLoanDelete(loan);
        expectLawful(can);
        std::optional<LeanBrokerPoolResult> result;
        if (can.ter == tesSUCCESS)
            result = leanLoanDelete(loan, pool);

        env(loan::del(f.borrower, loanKeylet.key), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Vault const cppPool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LoanBroker const cppBroker = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!can.leanError.has_value(), "lean canDelete error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), "lean delete error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        expectTer(lean, cppTer, expected);
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return;
        BEAST_EXPECT(!env.le(loanKeylet));
        expectVaultMatches(*this, result->pool, cppPool);
        expectBrokerMatches(*this, result->broker, cppBroker);
    }

    // The vault sits at its open limit, so the interest of a new loan does not fit.
    void
    testLoanInterestPastOpenLimit()
    {
        using namespace jtx;
        testcase("LoanSet: loan interest past the vault's open limit");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{}, Number{kOpenLimitUnits, -6});
        depositCover(env, f, Number{500});
        compareLoanSet(env, f, LoanParams{.interestRate = 10'000}, tecLIMIT_EXCEEDED);
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
        compareAccept(env, f, loanKeylet, p, tecLIMIT_EXCEEDED);
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
        // The late instalment: 4e9 of principal plus about 1.1e9 of late interest.
        env(loan::pay(f.borrower, loanKeylet.key, f.asset(Number{6, 9}), tfLoanLatePayment),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const v = readVaultState(env, f.vaultKeylet, f.asset.raw());
        Number const coarse{1, 10};
        BEAST_EXPECTS(v.assetsTotal >= coarse, "vault total " + to_string(v.assetsTotal));
        compareLoanSet(env, f, LoanParams{}, tecLIMIT_EXCEEDED);
    }

    // The vault phase is judged at the parent close time: a LoanSet exactly at the subscription
    // date is still too soon, exactly at the redemption date already expired.
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
        compareLoanSet(env, f, LoanParams{}, atRedemption ? tecEXPIRED : tecTOO_SOON);
    }

    // A proposal expires at its start date, judged at the parent close time.
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
        compareAccept(env, f, loanKeylet, p, tecEXPIRED);
    }

    enum class LoanKind : std::uint8_t { active, pending, paidOff };

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
        runLoanSet(
            "final payment too close to the redemption date",
            LoanParams{.paymentInterval = 500'000},
            tecNO_PERMISSION);
        runLoanSet(
            "principal above the vault's available assets",
            LoanParams{.principal = Number{20'000}},
            tecINSUFFICIENT_FUNDS,
            Number{5'000});
        runLoanSet(
            "principal above the debt maximum",
            LoanParams{},
            tecLIMIT_EXCEEDED,
            Number{500},
            Number{500});
        runLoanSet("not enough cover", LoanParams{}, tecINSUFFICIENT_FUNDS, Number{0});
        runLoanSet(
            "fee off the vault grid",
            LoanParams{.originationFee = Number{1, -7}},
            tecPRECISION_LOSS);
        // One grid unit in three instalments: the rounded-up instalment covers the whole loan in
        // one payment, so the schedule cannot be honoured.
        runLoanSet(
            "principal too small for its instalments",
            LoanParams{.principal = Number{1, -6}, .paymentTotal = 3},
            tecPRECISION_LOSS);
        runLoanSet(
            "schedule past the protocol time limit",
            LoanParams{.paymentInterval = 4'000'000'000},
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
        // A tiny rate over many instalments (rate times count still below 1e-9): the binomial
        // series converges before its last term.
        runLoanSet(
            "tiny interest rate over 50 instalments",
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

        // Two-step proposals
        {
            testcase("LoanSet: two-step proposal");
            jtx::Env env(*this);
            auto const f = setUpBrokerVault(env, BrokerConfig{});
            depositCover(env, f, Number{500});
            compareLoanSet(
                env, f, LoanParams{.startDate = parentCloseTime(env) + 1'000}, tesSUCCESS);
        }
        {
            testcase("LoanSet: two-step proposal with an expired start date");
            jtx::Env env(*this);
            auto const f = setUpBrokerVault(env, BrokerConfig{});
            depositCover(env, f, Number{500});
            compareLoanSet(env, f, LoanParams{.startDate = parentCloseTime(env) - 10}, tecEXPIRED);
        }

        // Start dates are judged at the parent close time, not the ledger close time.
        {
            testcase("LoanSet: two-step proposal starting at the parent close time");
            jtx::Env env(*this);
            auto const f = setUpBrokerVault(env, BrokerConfig{});
            depositCover(env, f, Number{500});
            compareLoanSet(env, f, LoanParams{.startDate = parentCloseTime(env)}, tecEXPIRED);
        }
        {
            testcase("LoanSet: two-step proposal starting one second after the parent close time");
            jtx::Env env(*this);
            auto const f = setUpBrokerVault(env, BrokerConfig{});
            depositCover(env, f, Number{500});
            compareLoanSet(env, f, LoanParams{.startDate = parentCloseTime(env) + 1}, tesSUCCESS);
        }
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
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanSet, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
