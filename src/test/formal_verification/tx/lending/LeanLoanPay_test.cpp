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
#include <test/jtx/fee.h>
#include <test/jtx/pay.h>
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

// Differential tests of LoanPay: regular, late, full and overpayment payments. On success the
// loan, vault and broker post-states must match, and the model's amounts to the pool and to the
// broker must be what the ledger moved.
class LeanLoanPay_test : public LeanSuite
{
    static std::uint32_t
    flagsOf(PaymentType type)
    {
        switch (type)
        {
            case PaymentType::regular:
                return 0;
            case PaymentType::late:
                return tfLoanLatePayment;
            case PaymentType::full:
                return tfLoanFullPayment;
            case PaymentType::overpayment:
                return tfLoanOverpayment;
        }
        return 0;
    }

    static std::string
    typeName(PaymentType type)
    {
        switch (type)
        {
            case PaymentType::regular:
                return "regular";
            case PaymentType::late:
                return "late";
            case PaymentType::full:
                return "full";
            case PaymentType::overpayment:
                return "overpayment";
        }
        return "?";
    }

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
    comparePay(
        jtx::Env& env,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        PaymentType type,
        Number const& amount,
        TER expected)
    {
        using namespace jtx;
        Loan const loan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        std::uint32_t const now = parentCloseTime(env);

        LawfulTerResult const can = leanCanLoanPay(loan, type);
        expectLawful(can);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS)
            result = leanLoanPay(loan, pool, type, amount, now);

        Number const ownerBefore = assetBalance(env, f.owner, f.asset);
        // LoanPay's fee grows with the instalments one transaction may settle (up to 100).
        env(loan::pay(f.borrower, loanKeylet.key, f.asset(amount), flagsOf(type)),
            Fee(env.current()->fees().base * 101),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Loan const cppLoan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const cppPool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        Number const ownerAfter = assetBalance(env, f.owner, f.asset);
        env.close();

        BEAST_EXPECTS(!can.leanError.has_value(), "lean canPay error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), "lean pay error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        expectTer(lean, cppTer, expected);
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return;

        expectLoanMatches(*this, result->loan, cppLoan);
        expectVaultMatches(*this, result->pool, cppPool);
        expectBrokerMatches(*this, result->loan.broker, cppLoan.broker);
        // The pool receives principal and interest; the broker's fee goes to its cover or, once
        // the cover meets its minimum, to the owner.
        expectNumber(
            *this,
            "amount to pool",
            result->amountToPool,
            cppPool.assetsAvailable - pool.assetsAvailable);
        expectNumber(
            *this,
            "amount to broker",
            result->amountToBroker,
            (cppLoan.broker.coverAvailable - loan.broker.coverAvailable) +
                (ownerAfter - ownerBefore));
    }

    // One payment on `view`: C++ applies it there, the model runs on the same pre-state. The
    // verdicts must agree and, on success, so must the post-states and the amounts moved.
    // Returns the C++ verdict.
    TER
    checkPay(
        jtx::Env& env,
        OpenView& view,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        std::uint32_t paymentTotal,
        PaymentType type,
        Number const& amount,
        std::string const& at = {})
    {
        using namespace jtx;
        Asset const asset = f.asset.raw();
        Loan const loan = readLoan(view, loanKeylet, asset, paymentTotal);
        Vault const pool = readVaultState(view, f.vaultKeylet, asset);
        std::uint32_t const now = parentCloseTime(env);

        LawfulTerResult const can = leanCanLoanPay(loan, type);
        expectLawful(can);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS && !can.leanError)
            result = leanLoanPay(loan, pool, type, amount, now);

        Number const ownerBefore = holding(view, f.owner, asset);
        // LoanPay's fee grows with the instalments one transaction may settle (up to 100).
        TER const cppTer = applyOn(
            env,
            view,
            f.borrower,
            loan::pay(f.borrower, loanKeylet.key, f.asset(amount), flagsOf(type)),
            Fee(env.current()->fees().base * 101));

        BEAST_EXPECTS(!can.leanError.has_value(), at + "lean canPay error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), at + "lean pay error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        BEAST_EXPECTS(
            lean == cppTer, at + "cpp=" + transToken(cppTer) + " lean=" + transToken(lean));
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return cppTer;

        Loan const cppLoan = readLoan(view, loanKeylet, asset, paymentTotal);
        Vault const cppPool = readVaultState(view, f.vaultKeylet, asset);
        expectLoanMatches(*this, result->loan, cppLoan);
        expectVaultMatches(*this, result->pool, cppPool);
        expectBrokerMatches(*this, result->loan.broker, cppLoan.broker);
        expectNumber(
            *this,
            "amount to pool",
            result->amountToPool,
            cppPool.assetsAvailable - pool.assetsAvailable);
        expectNumber(
            *this,
            "amount to broker",
            result->amountToBroker,
            (cppLoan.broker.coverAvailable - loan.broker.coverAvailable) +
                (holding(view, f.owner, asset) - ownerBefore));
        return cppTer;
    }

    void
    expectPay(
        jtx::Env& env,
        OpenView& view,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        PaymentType type,
        Number const& amount,
        TER expected)
    {
        TER const cpp = checkPay(env, view, f, loanKeylet, p.paymentTotal, type, amount);
        BEAST_EXPECTS(
            cpp == expected,
            std::string("cpp=") + transToken(cpp) + " expected " + transToken(expected));
    }

    // A loan with `p` on a throwaway view of the fixture (broker cover 500), started `delay`
    // seconds before the parent close time, then paid.
    enum class LoanKind : std::uint8_t { active, pending, paidOff };

    void
    runPay(
        jtx::Env& env,
        BrokerFixture const& f,
        std::string const& label,
        LoanParams const& p0,
        std::uint32_t delay,
        PaymentType type,
        Number const& amount,
        TER expected,
        LoanKind kind = LoanKind::active)
    {
        using namespace jtx;
        testcase(
            typeName(type) + " payment: " + label +
            (f.asset.raw().holds<MPTIssue>() ? " (MPT)" : ""));

        OpenView view{*env.current()};
        std::uint32_t const now = parentCloseTime(env);
        LoanParams p = p0;
        if (kind == LoanKind::pending)
            p.startDate = now + 1'000;
        if (kind == LoanKind::paidOff)
            p.paymentTotal = 1;
        auto const loanKeylet = createLoan(env, view, f, p);
        if (kind != LoanKind::pending)
            startedAgo(view, loanKeylet, now, delay);
        if (kind == LoanKind::paidOff)
        {
            BEAST_EXPECT(
                applyOn(
                    env,
                    view,
                    f.borrower,
                    loan::pay(f.borrower, loanKeylet.key, f.asset(1'000)),
                    Fee(env.current()->fees().base * 101)) == tesSUCCESS);
        }
        expectPay(env, view, f, loanKeylet, p, type, amount, expected);
    }

    // Two regular installments paid in two transactions: the second one closes the loan.
    void
    testTwoInstallments(jtx::Env& env, BrokerFixture const& f)
    {
        testcase("regular payment: second installment closes the loan");

        OpenView view{*env.current()};
        LoanParams const p;
        auto const loanKeylet = createLoan(env, view, f, p);
        startedAgo(view, loanKeylet, parentCloseTime(env), 0);
        expectPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{500}, tesSUCCESS);
        expectPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{500}, tesSUCCESS);
    }

    // A payment on an impaired loan lifts the impairment. The loan must be late to be impaired,
    // so the payment is a late one.
    void
    testPayImpairedLoan(jtx::Env& env, BrokerFixture const& f)
    {
        using namespace jtx;
        testcase("late payment: on an impaired loan");

        OpenView view{*env.current()};
        LoanParams const p;
        auto const loanKeylet = createLoan(env, view, f, p);
        dueAt(view, loanKeylet, parentCloseTime(env), -1);
        BEAST_EXPECT(
            applyOn(env, view, f.owner, loan::manage(f.owner, loanKeylet.key, tfLoanImpair)) ==
            tesSUCCESS);
        BEAST_EXPECT(view.read(loanKeylet)->isFlag(lsfLoanImpaired));
        expectPay(env, view, f, loanKeylet, p, PaymentType::late, Number{600}, tesSUCCESS);
        BEAST_EXPECT(!view.read(loanKeylet)->isFlag(lsfLoanImpaired));
    }

    // A full payment after the first installment: right after an early installment the loan is
    // "paid ahead" (no interest accrues), after the due date interest accrues from it.
    void
    testFullAfterInstallment(jtx::Env& env, BrokerFixture const& f, bool pastDueDate)
    {
        testcase(
            std::string("full payment: after an installment, ") +
            (pastDueDate ? "past its due date" : "paid ahead"));

        OpenView view{*env.current()};
        std::uint32_t const now = parentCloseTime(env);
        LoanParams const p{.interestRate = 10'000, .paymentTotal = 3};
        auto const loanKeylet = createLoan(env, view, f, p);
        startedAgo(view, loanKeylet, now, 0);
        expectPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{400}, tesSUCCESS);
        if (pastDueDate)
        {
            std::uint32_t const prevDue = view.read(loanKeylet)->at(sfPreviousPaymentDueDate);
            ageLoan(view, loanKeylet, std::int64_t{prevDue} - (now - 1));
        }
        expectPay(env, view, f, loanKeylet, p, PaymentType::full, Number{800}, tesSUCCESS);
    }

    // Every installment of an interest-bearing loan paid one at a time.
    void
    testSequentialInstallments(jtx::Env& env, BrokerFixture const& f)
    {
        testcase("regular payment: three interest-bearing installments in turn");

        OpenView view{*env.current()};
        LoanParams const p{.interestRate = 10'000, .paymentTotal = 3};
        auto const loanKeylet = createLoan(env, view, f, p);
        startedAgo(view, loanKeylet, parentCloseTime(env), 0);
        for (int i = 0; i < 3; ++i)
            expectPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{400}, tesSUCCESS);
        BEAST_EXPECT(view.read(loanKeylet)->at(sfPaymentRemaining) == 0);
    }

    // The service fee goes into the broker's cover when the cover is below its minimum: a
    // defaulted loan with a 100% liquidation rate drains the cover first.
    void
    testFeeIntoCover()
    {
        using namespace jtx;
        testcase("regular payment: fee tops up a drained cover");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{.coverRateLiquidation = 100'000});
        depositCover(env, f, Number{200});
        auto const defaulting = submitLoanSet(env, f, LoanParams{});
        LoanParams const p{.serviceFee = Number{1}, .paymentInterval = 5'000};
        auto const paying = submitLoanSet(env, f, p);
        std::uint32_t const dueDate = env.le(defaulting)->at(sfNextPaymentDueDate);
        closeAt(env, dueDate + 61);
        env(loan::manage(f.owner, defaulting.key, tfLoanDefault), jtx::Ter(tesSUCCESS));
        env.close();
        BEAST_EXPECT(Number(env.le(f.brokerKeylet)->at(sfCoverAvailable)) == Number{0});
        comparePay(env, f, paying, p, PaymentType::regular, Number{501}, tesSUCCESS);
    }

    // Replay a payment history found by the model-only search (lean-coverage/Search.lean): a broker
    // without cover rates on a large vault, one loan, then the overpayments in order.
    void
    replayOverpayments(
        std::string const& label,
        LoanParams const& p,
        std::uint16_t managementFeeRate,
        std::vector<Number> const& amounts)
    {
        using namespace jtx;
        testcase("overpayment payment: " + label);

        Env env(*this);
        auto const f = setUpBrokerVault(
            env,
            BrokerConfig{
                .managementFeeRate = managementFeeRate,
                .coverRateMinimum = std::nullopt,
                .coverRateLiquidation = std::nullopt},
            Number{1, 9},
            false,
            true,
            LendingAsset::iou,
            std::chrono::seconds{900'000'000});
        // Keep the owner's balance small, so its trust line records the exact fee it receives.
        env(pay(f.owner, f.issuer, f.asset(Number{1, 10} - Number{1'000})));
        env.close();
        auto const loanKeylet = submitLoanSet(env, f, p);
        for (auto const& amount : amounts)
            comparePay(env, f, loanKeylet, p, PaymentType::overpayment, amount, tesSUCCESS);
    }

    // ---- Sweeps ----

    struct SweepFixture
    {
        jtx::Env& env;
        BrokerFixture f;
    };
    using SweepFixtures = std::vector<SweepFixture>;

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
            kind);
        // Keep the owner's IOU balance small, so its trust line records the exact fee it receives.
        if (kind == LendingAsset::iou)
            env(jtx::pay(f.owner, f.issuer, f.asset(Number{1, 10} - Number{1'000})));
        // Staged due dates lie up to 1000 s before the parent close time.
        env.close(env.now() + std::chrono::seconds{100'000});
        return f;
    }

    void
    testDueDateSweep(SweepFixtures const& fixtures)
    {
        for (auto const& [env, f] : fixtures)
        {
            sweepDueDate(env, f);
        }
    }

    // Lateness: regular, full and overpayments are tecEXPIRED once the parent close time passes
    // the due date, a late payment is tecTOO_SOON until then. The amount is the exact amount due.
    void
    sweepDueDate(jtx::Env& env, BrokerFixture const& f)
    {
        beginCase(("LoanPay " + assetName(f) + " due date-Sweep").c_str());
        std::uint32_t const now = parentCloseTime(env);
        runAroundCusp(kDueDateCases, [&](DueDateCusp const& c) {
            OpenView view{*env.current()};
            LoanParams const p{
                .principal = units(f, c.principal),
                .allowsOverpayment = c.type == PaymentType::overpayment};
            auto const loan = createLoan(env, view, f, p);
            dueAt(view, loan, now, c.dueOffset);
            return checkPay(
                env, view, f, loan, p.paymentTotal, c.type, units(f, c.amount), describe(c) + ": ");
        });
    }

    void
    testLateInterestSweep(SweepFixtures const& fixtures)
    {
        for (auto const& [env, f] : fixtures)
        {
            sweepLateInterest(env, f);
        }
    }

    // Late amount due: one installment, its fees and the late interest (exactly k units per second
    // late at these principals). Below it is tecINSUFFICIENT_PAYMENT; not late is tecTOO_SOON.
    void
    sweepLateInterest(jtx::Env& env, BrokerFixture const& f)
    {
        beginCase(("LoanPay " + assetName(f) + " late interest-Sweep").c_str());
        std::uint32_t const now = parentCloseTime(env);
        runAroundCusp(kLateInterestCases, [&](LateInterestCusp const& c) {
            OpenView view{*env.current()};
            LoanParams const p{
                .principal = units(f, kSecondsPerYear * c.k),
                .lateInterestRate = static_cast<std::uint32_t>(kRateCap),
                .serviceFee = units(f, c.serviceFee),
                .latePaymentFee = units(f, c.lateFee),
                .paymentTotal = c.installments};
            auto const loan = createLoan(env, view, f, p);
            dueAt(view, loan, now, -c.lateBy);
            return checkPay(
                env,
                view,
                f,
                loan,
                p.paymentTotal,
                PaymentType::late,
                units(f, c.amount),
                describe(c) + ": ");
        });
    }

    void
    testServiceFeeSweep(SweepFixtures const& fixtures)
    {
        for (auto const& [env, f] : fixtures)
        {
            sweepServiceFee(env, f);
        }
    }

    // A regular payment must cover one installment and its service fee, else
    // tecINSUFFICIENT_PAYMENT.
    void
    sweepServiceFee(jtx::Env& env, BrokerFixture const& f)
    {
        beginCase(("LoanPay " + assetName(f) + " service fee-Sweep").c_str());
        std::uint32_t const now = parentCloseTime(env);
        runAroundCusp(kServiceFeeCases, [&](ServiceFeeCusp const& c) {
            OpenView view{*env.current()};
            LoanParams const p{
                .principal = units(f, 2 * c.installment), .serviceFee = units(f, c.serviceFee)};
            auto const loan = createLoan(env, view, f, p);
            startedAgo(view, loan, now, 0);
            return checkPay(
                env,
                view,
                f,
                loan,
                p.paymentTotal,
                PaymentType::regular,
                units(f, c.amount),
                describe(c) + ": ");
        });
    }

    void
    testFullPaymentSweep(SweepFixtures const& fixtures)
    {
        for (auto const& [env, f] : fixtures)
        {
            sweepFullPayment(env, f);
        }
    }

    // A full payment must cover the principal, the close interest and the close payment fee, else
    // tecINSUFFICIENT_PAYMENT.
    void
    sweepFullPayment(jtx::Env& env, BrokerFixture const& f)
    {
        beginCase(("LoanPay " + assetName(f) + " full payment-Sweep").c_str());
        std::uint32_t const now = parentCloseTime(env);
        runAroundCusp(kFullPaymentCases, [&](FullPaymentCusp const& c) {
            OpenView view{*env.current()};
            LoanParams const p{
                .principal = units(f, c.principal),
                .closeInterestRate = c.closeRate,
                .closePaymentFee = units(f, c.closeFee)};
            auto const loan = createLoan(env, view, f, p);
            startedAgo(view, loan, now, 0);
            return checkPay(
                env,
                view,
                f,
                loan,
                p.paymentTotal,
                PaymentType::full,
                units(f, c.amount),
                describe(c) + ": ");
        });
    }

    void
    runTests() override
    {
        // The single-value tests share one fixture per asset (broker cover 500); each test runs
        // on a throwaway view of it.
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

        // Regular payments on a 1000 loan in two installments of 500 (no interest).
        runPay(
            env,
            iou,
            "one installment",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{500},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "both installments in one transaction",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{1'000},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "amount below one installment",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{499},
            tecINSUFFICIENT_PAYMENT);
        runPay(
            env,
            iou,
            "one installment with interest",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            0,
            PaymentType::regular,
            Number{400},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "one installment with a service fee",
            LoanParams{.serviceFee = Number{1}},
            0,
            PaymentType::regular,
            Number{501},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "when late",
            LoanParams{},
            601,
            PaymentType::regular,
            Number{500},
            tecEXPIRED);
        runPay(
            env,
            iou,
            "on a pending proposal",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{500},
            tecNO_PERMISSION,
            LoanKind::pending);
        runPay(
            env,
            iou,
            "on a paid-off loan",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{500},
            tecKILLED,
            LoanKind::paidOff);
        testTwoInstallments(env, iou);

        // Late payments
        runPay(
            env,
            iou,
            "one installment",
            LoanParams{.lateInterestRate = 10'000, .latePaymentFee = Number{2}},
            601,
            PaymentType::late,
            Number{600},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "before the due date",
            LoanParams{},
            0,
            PaymentType::late,
            Number{600},
            tecTOO_SOON);
        runPay(
            env,
            iou,
            "without a late rate or fee",
            LoanParams{},
            601,
            PaymentType::late,
            Number{500},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "amount below the installment",
            LoanParams{},
            601,
            PaymentType::late,
            Number{100},
            tecINSUFFICIENT_PAYMENT);
        testPayImpairedLoan(env, iou);
        // One transaction settles at most 100 installments.
        runPay(
            env,
            iou,
            "stops at 100 installments",
            LoanParams{.principal = Number{1'500}, .paymentTotal = 150},
            0,
            PaymentType::regular,
            Number{1'500},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "stops at 100 installments",
            LoanParams{.principal = Number{1'500}, .paymentTotal = 150, .allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{1'500},
            tesSUCCESS);

        // Full payments
        runPay(
            env,
            iou,
            "below the amount due",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            100,
            PaymentType::full,
            Number{900},
            tecINSUFFICIENT_PAYMENT);
        runPay(
            env,
            iou,
            "pay off a three-installment loan",
            LoanParams{.interestRate = 10'000, .closeInterestRate = 1'000, .paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'100},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "without a close rate",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'100},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "when late",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            601,
            PaymentType::full,
            Number{1'100},
            tecEXPIRED);
        runPay(
            env,
            iou,
            "on a zero-interest loan",
            LoanParams{.paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'000},
            tesSUCCESS);
        testFullAfterInstallment(env, iou, false);
        testFullAfterInstallment(env, iou, true);
        runPay(
            env,
            iou,
            "with one installment left",
            LoanParams{.paymentTotal = 1},
            0,
            PaymentType::full,
            Number{1'100},
            tecKILLED);

        testSequentialInstallments(env, iou);
        testFeeIntoCover();

        // Histories found by the model-only search. In each, the scheduled part is paid and the
        // overpayment tail is dropped (or trimmed) by a re-amortization or delta guard.
        replayOverpayments(
            "re-amortized schedule fails its guards",
            LoanParams{
                .principal = Number{6'277, -3},
                .interestRate = 6'291,
                .overpaymentInterestRate = 5'447,
                .overpaymentFee = 70'236,
                .paymentInterval = 1'455'452,
                .paymentTotal = 365,
                .allowsOverpayment = true},
            4'157,
            {Number{198'638'654'596'208LL, -15}});
        replayOverpayments(
            "re-amortization would raise the interest",
            LoanParams{
                .principal = Number{69'720},
                .interestRate = 14'830,
                .overpaymentInterestRate = 8'433,
                .overpaymentFee = 1'310,
                .paymentInterval = 82'174,
                .paymentTotal = 53,
                .allowsOverpayment = true},
            4'962,
            {Number{398'774'831'464'331LL, -11}, Number{1'329'242'358'868'834LL, -12}});
        replayOverpayments(
            "management fee delta floored at zero",
            LoanParams{
                .principal = Number{219, -4},
                .interestRate = 64'661,
                .overpaymentInterestRate = 77'504,
                .overpaymentFee = 69'802,
                .paymentInterval = 4'646,
                .paymentTotal = 169,
                .allowsOverpayment = true},
            9'451,
            {Number{3'117'013'163'787'732LL, -14}});

        // MPT vault
        runPay(
            mptEnv,
            mpt,
            "one installment with interest",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            0,
            PaymentType::regular,
            Number{400},
            tesSUCCESS);
        runPay(
            mptEnv,
            mpt,
            "one installment",
            LoanParams{.lateInterestRate = 10'000, .latePaymentFee = Number{2}},
            601,
            PaymentType::late,
            Number{600},
            tesSUCCESS);
        runPay(
            mptEnv,
            mpt,
            "pay off a three-installment loan",
            LoanParams{.interestRate = 10'000, .closeInterestRate = 1'000, .paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'100},
            tesSUCCESS);

        // Overpayments
        runPay(
            env,
            iou,
            "amount clears the whole loan",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3, .allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{1'200},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "extra below one grid unit",
            LoanParams{.allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{5'000'000'005LL, -7},
            tesSUCCESS);
        // A 100% overpayment fee consumes the extra, so no principal is paid down.
        runPay(
            env,
            iou,
            "extra consumed by the overpayment fee",
            LoanParams{.overpaymentFee = 100'000, .paymentTotal = 3, .allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{600},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "one installment plus extra principal",
            LoanParams{
                .interestRate = 10'000,
                .overpaymentInterestRate = 1'000,
                .overpaymentFee = 500,
                .paymentTotal = 4,
                .allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{500},
            tesSUCCESS);
        runPay(
            env,
            iou,
            "on a loan that forbids it",
            LoanParams{},
            0,
            PaymentType::overpayment,
            Number{600},
            tecNO_PERMISSION);

        // Sweeps: one fixture per asset, no cover rates, 9e9 units in the vault.
        jtx::Env iouSweepEnv(*this);
        jtx::Env mptSweepEnv(*this);
        SweepFixtures const fixtures{
            {iouSweepEnv, sweepFixture(iouSweepEnv, LendingAsset::iou)},
            {mptSweepEnv, sweepFixture(mptSweepEnv, LendingAsset::mpt)}};
        testDueDateSweep(fixtures);
        testLateInterestSweep(fixtures);
        testServiceFeeSweep(fixtures);
        testFullPaymentSweep(fixtures);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanPay, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
