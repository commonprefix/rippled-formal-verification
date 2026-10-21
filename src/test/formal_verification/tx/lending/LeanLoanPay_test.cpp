#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

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
        env(loan::pay(f.borrower, loanKeylet.key, f.asset(amount), flagsOf(type)),
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

    // Set up a broker (cover 500) and a loan with `p`, advance `delay` seconds past the loan's
    // start, then pay.
    enum class LoanKind : std::uint8_t { active, pending, paidOff };

    void
    runPay(
        std::string const& label,
        LoanParams const& p0,
        std::uint32_t delay,
        PaymentType type,
        Number const& amount,
        TER expected,
        LoanKind kind = LoanKind::active,
        LendingAsset assetKind = LendingAsset::iou)
    {
        using namespace jtx;
        testcase(
            typeName(type) + " payment: " + label +
            (assetKind == LendingAsset::mpt ? " (MPT)" : ""));

        Env env(*this);
        auto const f =
            setUpBrokerVault(env, BrokerConfig{}, Number{10'000}, false, true, assetKind);
        depositCover(env, f, Number{500});
        LoanParams p = p0;
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
        if (delay != 0)
            closeAt(env, parentCloseTime(env) + delay);
        comparePay(env, f, loanKeylet, p, type, amount, expected);
    }

    // Two regular instalments paid in two transactions: the second one closes the loan.
    void
    testTwoInstalments()
    {
        using namespace jtx;
        testcase("regular payment: second instalment closes the loan");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams const p;
        auto const loanKeylet = submitLoanSet(env, f, p);
        comparePay(env, f, loanKeylet, p, PaymentType::regular, Number{500}, tesSUCCESS);
        comparePay(env, f, loanKeylet, p, PaymentType::regular, Number{500}, tesSUCCESS);
    }

    // A payment on an impaired loan lifts the impairment. The loan must be late to be impaired,
    // so the payment is a late one.
    void
    testPayImpairedLoan()
    {
        using namespace jtx;
        testcase("late payment: on an impaired loan");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams const p;
        auto const loanKeylet = submitLoanSet(env, f, p);
        std::uint32_t const dueDate = env.le(loanKeylet)->at(sfNextPaymentDueDate);
        closeAt(env, dueDate + 1);
        env(loan::manage(f.owner, loanKeylet.key, tfLoanImpair), jtx::Ter(tesSUCCESS));
        env.close();
        BEAST_EXPECT(env.le(loanKeylet)->isFlag(lsfLoanImpaired));
        comparePay(env, f, loanKeylet, p, PaymentType::late, Number{600}, tesSUCCESS);
        BEAST_EXPECT(!env.le(loanKeylet)->isFlag(lsfLoanImpaired));
    }

    // A full payment after the first instalment: right after an early instalment the loan is
    // "paid ahead" (no interest accrues), after the due date interest accrues from it.
    void
    testFullAfterInstalment(bool pastDueDate)
    {
        using namespace jtx;
        testcase(
            std::string("full payment: after an instalment, ") +
            (pastDueDate ? "past its due date" : "paid ahead"));

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams const p{.interestRate = 10'000, .paymentTotal = 3};
        auto const loanKeylet = submitLoanSet(env, f, p);
        comparePay(env, f, loanKeylet, p, PaymentType::regular, Number{400}, tesSUCCESS);
        if (pastDueDate)
        {
            std::uint32_t const prevDue = env.le(loanKeylet)->at(sfPreviousPaymentDueDate);
            closeAt(env, prevDue + 1);
        }
        comparePay(env, f, loanKeylet, p, PaymentType::full, Number{800}, tesSUCCESS);
    }

    // Every instalment of an interest-bearing loan paid one at a time.
    void
    testSequentialInstalments()
    {
        using namespace jtx;
        testcase("regular payment: three interest-bearing instalments in turn");

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams const p{.interestRate = 10'000, .paymentTotal = 3};
        auto const loanKeylet = submitLoanSet(env, f, p);
        for (int i = 0; i < 3; ++i)
            comparePay(env, f, loanKeylet, p, PaymentType::regular, Number{400}, tesSUCCESS);
        BEAST_EXPECT(env.le(loanKeylet)->at(sfPaymentRemaining) == 0);
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

    void
    runTests() override
    {
        // Regular payments on a 1000 loan in two instalments of 500 (no interest).
        runPay("one instalment", LoanParams{}, 0, PaymentType::regular, Number{500}, tesSUCCESS);
        runPay(
            "both instalments in one transaction",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{1'000},
            tesSUCCESS);
        runPay(
            "amount below one instalment",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{499},
            tecINSUFFICIENT_PAYMENT);
        runPay(
            "one instalment with interest",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            0,
            PaymentType::regular,
            Number{400},
            tesSUCCESS);
        runPay(
            "one instalment with a service fee",
            LoanParams{.serviceFee = Number{1}},
            0,
            PaymentType::regular,
            Number{501},
            tesSUCCESS);
        runPay("when late", LoanParams{}, 601, PaymentType::regular, Number{500}, tecEXPIRED);
        runPay(
            "on a pending proposal",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{500},
            tecNO_PERMISSION,
            LoanKind::pending);
        runPay(
            "on a paid-off loan",
            LoanParams{},
            0,
            PaymentType::regular,
            Number{500},
            tecKILLED,
            LoanKind::paidOff);
        testTwoInstalments();

        // Late payments
        runPay(
            "one instalment",
            LoanParams{.lateInterestRate = 10'000, .latePaymentFee = Number{2}},
            601,
            PaymentType::late,
            Number{600},
            tesSUCCESS);
        runPay("before the due date", LoanParams{}, 0, PaymentType::late, Number{600}, tecTOO_SOON);
        runPay(
            "without a late rate or fee",
            LoanParams{},
            601,
            PaymentType::late,
            Number{500},
            tesSUCCESS);
        runPay(
            "amount below the instalment",
            LoanParams{},
            601,
            PaymentType::late,
            Number{100},
            tecINSUFFICIENT_PAYMENT);
        testPayImpairedLoan();

        // Full payments
        runPay(
            "pay off a three-instalment loan",
            LoanParams{.interestRate = 10'000, .closeInterestRate = 1'000, .paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'100},
            tesSUCCESS);
        runPay(
            "without a close rate",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'100},
            tesSUCCESS);
        runPay(
            "when late",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            601,
            PaymentType::full,
            Number{1'100},
            tecEXPIRED);
        runPay(
            "on a zero-interest loan",
            LoanParams{.paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'000},
            tesSUCCESS);
        testFullAfterInstalment(false);
        testFullAfterInstalment(true);
        runPay(
            "with one instalment left",
            LoanParams{.paymentTotal = 1},
            0,
            PaymentType::full,
            Number{1'100},
            tecKILLED);

        testSequentialInstalments();
        testFeeIntoCover();

        // MPT vault
        runPay(
            "one instalment with interest",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3},
            0,
            PaymentType::regular,
            Number{400},
            tesSUCCESS,
            LoanKind::active,
            LendingAsset::mpt);
        runPay(
            "one instalment",
            LoanParams{.lateInterestRate = 10'000, .latePaymentFee = Number{2}},
            601,
            PaymentType::late,
            Number{600},
            tesSUCCESS,
            LoanKind::active,
            LendingAsset::mpt);
        runPay(
            "pay off a three-instalment loan",
            LoanParams{.interestRate = 10'000, .closeInterestRate = 1'000, .paymentTotal = 3},
            100,
            PaymentType::full,
            Number{1'100},
            tesSUCCESS,
            LoanKind::active,
            LendingAsset::mpt);

        // Overpayments
        runPay(
            "amount clears the whole loan",
            LoanParams{.interestRate = 10'000, .paymentTotal = 3, .allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{1'200},
            tesSUCCESS);
        runPay(
            "extra below one grid unit",
            LoanParams{.allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{5'000'000'005LL, -7},
            tesSUCCESS);
        // A 100% overpayment fee consumes the extra, so no principal is paid down.
        runPay(
            "extra consumed by the overpayment fee",
            LoanParams{.overpaymentFee = 100'000, .paymentTotal = 3, .allowsOverpayment = true},
            0,
            PaymentType::overpayment,
            Number{600},
            tesSUCCESS);
        runPay(
            "one instalment plus extra principal",
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
            "on a loan that forbids it",
            LoanParams{},
            0,
            PaymentType::overpayment,
            Number{600},
            tecNO_PERMISSION);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanPay, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
