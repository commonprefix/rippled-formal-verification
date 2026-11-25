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
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// A LoanPay of `amount` units on a loan of `principal` units in `paymentTotal` installments
// `paymentInterval` s apart, without interest unless a rate is set, with the vault in its
// investment phase. The loan starts at the parent close time P, or its next payment falls due at
// P + `due`. `stage` (cover and minimum cover rate), then the vault's `available` assets, are
// staged after the loan. Overpayment rows allow overpayments.
struct LoanPayCase
{
    PaymentType type{};
    std::int64_t principal{};
    std::uint32_t interestRate{};
    std::uint32_t lateInterestRate{};
    std::uint32_t closeInterestRate{};
    std::uint32_t overpaymentInterestRate{};
    std::uint32_t overpaymentFee{};
    std::int64_t serviceFee{};
    std::int64_t latePaymentFee{};
    std::int64_t closePaymentFee{};
    std::uint32_t paymentInterval{600};
    std::uint32_t paymentTotal{2};
    std::optional<std::int64_t> due{};
    LendingStage stage{};
    std::optional<std::int64_t> available{};
    std::int64_t amount{};
    TER expected;
};

// Differential tests of LoanPay: regular, late, full and overpayment payments. On success the
// loan, vault and broker post-states must match, and the model's amounts to the pool and to the
// broker must be what the ledger moved.
// Rows stage ledger state on a throwaway view, including states no transaction sequence may
// reach: a verdict compares model and C++ on the same pre-state, not a claim the state is
// reachable (see stageLending).
class LeanLoanPay_test : public LeanSuite
{
    // One payment on `view`: C++ applies it there, the model runs on the same pre-state.
    void
    checkPay(
        jtx::Env& env,
        OpenView& view,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        PaymentType type,
        Number const& amount,
        TER expected,
        std::string const& at = {})
    {
        AppliedLoanTx const cpp = applyLoanPay(env, view, f, loanKeylet, p, type, amount);
        expectSame(*this, at, cpp, leanLoanPay(cpp, type, amount), expected);
    }

    // One payment checked on a throwaway view of `env`, then applied to `env` itself and the
    // ledger closed, so the next payment comes later.
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
        OpenView view{*env.current()};
        checkPay(env, view, f, loanKeylet, p, type, amount, expected);
        env(loan::pay(f.borrower, loanKeylet.key, f.asset(amount), payFlags(type)),
            Fee(env.current()->fees().base * 101),
            jtx::Ter(expected));
        env.close();
    }

    // A loan with `p` on a throwaway view of the fixture (broker cover 500), started `delay`
    // seconds before the parent close time, then paid.
    void
    runPay(
        jtx::Env& env,
        BrokerFixture const& f,
        std::string const& what,
        LoanParams const& p0,
        std::uint32_t delay,
        PaymentType type,
        Number const& amount,
        TER expected,
        LoanKind kind = LoanKind::active)
    {
        using namespace jtx;
        std::string const label = paymentTypeName(type) + " payment: " + what +
            (f.asset.raw().holds<MPTIssue>() ? " (MPT)" : "");
        testcase(label);

        OpenView view{*env.current()};
        LoanParams p = p0;
        std::optional<Keylet> loanKeylet;
        if (!tryStage(
                *this,
                label,
                [&] {
                    loanKeylet = stageLoan(env, view, f, p, kind, parentCloseTime(env), delay);
                }) ||
            !loanKeylet)
            return;
        checkPay(env, view, f, *loanKeylet, p, type, amount, expected);
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
        checkPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{500}, tesSUCCESS);
        checkPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{500}, tesSUCCESS);
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
            applyOn(env, view, loan::manage(f.owner, loanKeylet.key, tfLoanImpair)) == tesSUCCESS);
        BEAST_EXPECT(view.read(loanKeylet)->isFlag(lsfLoanImpaired));
        checkPay(env, view, f, loanKeylet, p, PaymentType::late, Number{600}, tesSUCCESS);
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
        checkPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{400}, tesSUCCESS);
        if (pastDueDate)
        {
            std::uint32_t const prevDue = view.read(loanKeylet)->at(sfPreviousPaymentDueDate);
            ageLoan(view, loanKeylet, std::int64_t{prevDue} - (now - 1));
        }
        checkPay(env, view, f, loanKeylet, p, PaymentType::full, Number{800}, tesSUCCESS);
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
            checkPay(env, view, f, loanKeylet, p, PaymentType::regular, Number{400}, tesSUCCESS);
        BEAST_EXPECT(view.read(loanKeylet)->at(sfPaymentRemaining) == 0);
    }

    // The service fee goes into the broker's cover when the cover is below its minimum: a
    // defaulted loan with a 100% liquidation rate drains the cover first.
    void
    testFeeIntoCover()
    {
        using namespace jtx;
        testcase("regular payment: fee tops up a drained cover");

        Env env{*this, lendingTestAmendments()};
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

        Env env{*this, lendingTestAmendments()};
        auto const f = setUpBrokerVault(
            env,
            BrokerConfig{
                .managementFeeRate = managementFeeRate,
                .coverRateMinimum = std::nullopt,
                .coverRateLiquidation = std::nullopt,
            },
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

    // Each row stages the asset's shared ledger on a throwaway view: the vault in its investment
    // phase, the broker's management fee at 1% and no cover rate, the loan, then the row's stage;
    // the owner's IOU balance is zeroed so the fee it receives is exact. The row's payment must
    // give its verdict on both sides, with every field of the loan, its broker and the pool, and
    // the amounts to the pool and to the broker, equal when both succeed. Amounts are in units of
    // the vault grid.
    // A group comment names a boundary value (the cusp); its rows step those values around it.
    // - Due date: regular, full and overpayments of the exact amount due are tecEXPIRED once the
    //   due date is before P; a late payment is tecTOO_SOON until then, and an amount below the
    //   amount due is tecINSUFFICIENT_PAYMENT.
    // - Late interest: at a 100% late rate a principal of 31'536'000 * k accrues exactly k units
    //   per second late, so a late payment below principal / installments + service fee + late
    //   fee + k * seconds late is tecINSUFFICIENT_PAYMENT; not late (due at or after P) is
    //   tecTOO_SOON.
    // - Service fee: a regular payment below one installment plus its service fee is
    //   tecINSUFFICIENT_PAYMENT.
    // - Full payment: a full payment below the principal, the close interest
    //   (principal * close rate / 1e5) and the close fee is tecINSUFFICIENT_PAYMENT.
    // - Full payment of the last installment: a full payment with one installment left is
    //   tecKILLED; with two or three it pays the loan off.
    // - Fee routing: the one-unit service fee goes to the owner once the cover reaches the
    //   minimum cover ceil(debt * rate / 1e5), else into the cover; the verdict does not change.
    // - Regular with interest: at 100% a year over 31'536'000 s (periodic rate 1) a principal of
    //   3'153'600'000 in two installments pays 4'204'800'000 each; less is
    //   tecINSUFFICIENT_PAYMENT. Of the first installment's 3'153'600'000 interest the broker's 1%
    //   fee rounds to 31'535'999 (toBroker), the pool gets 4'173'264'001. For a principal of 3
    //   (installment 4) the fee rounds to nothing.
    // - Late with interest: a 100% late rate on 3'153'600'000 accrues 100 units a second, so
    //   1'000 s late the amount due is 4'204'900'000; 1% of the late interest also goes to the
    //   broker.
    // - Full with interest: at the start the amount due is the principal plus 10% close interest,
    //   3'468'960'000 (the broker gets 1% of the close interest, the schedule's fee is not owed);
    //   half an interval in it adds 1'576'800'000 accrued interest, 5'045'760'000. For a principal
    //   of 3 the 0.3 close interest rounds away.
    // - Overpayment with interest: 7'000'000'000 in three installments pays 7'999'999'999; an
    //   extra goes to the principal (1% fee, 10% overpayment interest) or is dropped by the
    //   re-amortization guards (only the 2-unit extra is applied here; for 7, extras 1, 2 and 4
    //   are).
    // - Credit below the vault grid (IOU): with 2e16 units available the vault's grid is 10 units,
    //   so a payment that does not close the loan and credits less than 10 is tecPRECISION_LOSS.
    // The due-date rules (late only once P is past the due date) are those of fixCleanup3_4_0.
    // clang-format off
    static constexpr LoanPayCase kDueDate[] = {
        // regular, principal 2, amount 1 due at P
        {.type = PaymentType::regular, .principal = 2, .due = -2, .amount = 1, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2, .due = -2, .amount = 2, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2, .due = -2, .amount = 3, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2, .due = -1, .amount = 1, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2, .due = -1, .amount = 2, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2, .due = -1, .amount = 3, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2, .due = 0, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 0, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 0, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 1, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 1, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 1, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 2, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 2, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .due = 2, .amount = 3, .expected = tesSUCCESS},
        // regular, principal 2'000'000'000, amount 1'000'000'000 due at P
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -2, .amount = 999'999'998, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -2, .amount = 999'999'999, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'000, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'001, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'002, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -1, .amount = 999'999'998, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -1, .amount = 999'999'999, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'000, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'001, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'002, .expected = tecEXPIRED},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 0, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 0, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 1, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 1, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 2, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 2, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // late, principal 2, amount 1 due at P
        {.type = PaymentType::late, .principal = 2, .due = -2, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2, .due = -2, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2, .due = -2, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2, .due = -1, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2, .due = -1, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2, .due = -1, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2, .due = 0, .amount = 1, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 0, .amount = 2, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 0, .amount = 3, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 1, .amount = 1, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 1, .amount = 2, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 1, .amount = 3, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 2, .amount = 1, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 2, .amount = 2, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2, .due = 2, .amount = 3, .expected = tecTOO_SOON},
        // late, principal 2'000'000'000, amount 1'000'000'000 due at P
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -2, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -2, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -1, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -1, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 0, .amount = 999'999'998, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 0, .amount = 999'999'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 1, .amount = 999'999'998, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 1, .amount = 999'999'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 2, .amount = 999'999'998, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 2, .amount = 999'999'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'002, .expected = tecTOO_SOON},
        // full, principal 2, amount 2 due at P
        {.type = PaymentType::full, .principal = 2, .due = -2, .amount = 1, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = -2, .amount = 2, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = -2, .amount = 3, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = -2, .amount = 4, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = -1, .amount = 1, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = -1, .amount = 2, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = -1, .amount = 3, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = -1, .amount = 4, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2, .due = 0, .amount = 1, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .due = 0, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 0, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 0, .amount = 4, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 1, .amount = 1, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .due = 1, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 1, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 1, .amount = 4, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 2, .amount = 1, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .due = 2, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 2, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .due = 2, .amount = 4, .expected = tesSUCCESS},
        // full, principal 2'000'000'000, amount 2'000'000'000 due at P
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -2, .amount = 1'999'999'998, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -2, .amount = 1'999'999'999, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -2, .amount = 2'000'000'000, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -2, .amount = 2'000'000'001, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -2, .amount = 2'000'000'002, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -1, .amount = 1'999'999'998, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -1, .amount = 1'999'999'999, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -1, .amount = 2'000'000'000, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -1, .amount = 2'000'000'001, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = -1, .amount = 2'000'000'002, .expected = tecEXPIRED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 0, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 0, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 0, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 0, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 0, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 1, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 1, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 1, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 1, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 1, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 2, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 2, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 2, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 2, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .due = 2, .amount = 2'000'000'002, .expected = tesSUCCESS},
        // overpayment, principal 2, amount 1 due at P
        {.type = PaymentType::overpayment, .principal = 2, .due = -2, .amount = 1, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2, .due = -2, .amount = 2, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2, .due = -2, .amount = 3, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2, .due = -1, .amount = 1, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2, .due = -1, .amount = 2, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2, .due = -1, .amount = 3, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2, .due = 0, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 0, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 0, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 1, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 1, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 1, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 2, .amount = 1, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 2, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2, .due = 2, .amount = 3, .expected = tesSUCCESS},
        // overpayment, principal 2'000'000'000, amount 1'000'000'000 due at P
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -2, .amount = 999'999'998, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -2, .amount = 999'999'999, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'000, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'001, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -2, .amount = 1'000'000'002, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -1, .amount = 999'999'998, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -1, .amount = 999'999'999, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'000, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'001, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = -1, .amount = 1'000'000'002, .expected = tecEXPIRED},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 0, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 0, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 0, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 1, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 1, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 1, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 2, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 2, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 2'000'000'000, .due = 2, .amount = 1'000'000'002, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kLateInterest[] = {
        // principal 31'536'000 in 2, service fee 0, late fee 0, 1 s late: amount 15'768'001
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 1, .amount = 15'767'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 1, .amount = 15'768'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 1, .amount = 15'768'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 1, .amount = 15'768'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 1, .amount = 15'768'003, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 0, .amount = 15'767'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 0, .amount = 15'768'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 0, .amount = 15'768'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 0, .amount = 15'768'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = 0, .amount = 15'768'003, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -1, .amount = 15'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -1, .amount = 15'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -1, .amount = 15'768'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -1, .amount = 15'768'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -1, .amount = 15'768'003, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -2, .amount = 15'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -2, .amount = 15'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -2, .amount = 15'768'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -2, .amount = 15'768'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -2, .amount = 15'768'003, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -3, .amount = 15'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -3, .amount = 15'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -3, .amount = 15'768'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -3, .amount = 15'768'002, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .due = -3, .amount = 15'768'003, .expected = tesSUCCESS},
        // principal 1'009'152'000 in 2, service fee 0, late fee 0, 1'000 s late: amount 504'608'000
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -998, .amount = 504'607'998, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -998, .amount = 504'607'999, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -998, .amount = 504'608'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -998, .amount = 504'608'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -998, .amount = 504'608'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -999, .amount = 504'607'998, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -999, .amount = 504'607'999, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -999, .amount = 504'608'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -999, .amount = 504'608'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -999, .amount = 504'608'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'000, .amount = 504'607'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'000, .amount = 504'607'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'000, .amount = 504'608'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'000, .amount = 504'608'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'000, .amount = 504'608'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'001, .amount = 504'607'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'001, .amount = 504'607'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'001, .amount = 504'608'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'001, .amount = 504'608'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'001, .amount = 504'608'002, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'002, .amount = 504'607'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'002, .amount = 504'607'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'002, .amount = 504'608'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'002, .amount = 504'608'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 1'009'152'000, .lateInterestRate = 100'000, .due = -1'002, .amount = 504'608'002, .expected = tecINSUFFICIENT_PAYMENT},
        // principal 31'536'000 in 1, service fee 0, late fee 0, 1'000 s late: amount 31'537'000
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -998, .amount = 31'536'998, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -998, .amount = 31'536'999, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -998, .amount = 31'537'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -998, .amount = 31'537'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -998, .amount = 31'537'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -999, .amount = 31'536'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -999, .amount = 31'536'999, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -999, .amount = 31'537'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -999, .amount = 31'537'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -999, .amount = 31'537'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'000, .amount = 31'536'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'000, .amount = 31'536'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'000, .amount = 31'537'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'000, .amount = 31'537'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'000, .amount = 31'537'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'001, .amount = 31'536'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'001, .amount = 31'536'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'001, .amount = 31'537'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'001, .amount = 31'537'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'001, .amount = 31'537'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'002, .amount = 31'536'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'002, .amount = 31'536'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'002, .amount = 31'537'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'002, .amount = 31'537'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .paymentTotal = 1, .due = -1'002, .amount = 31'537'002, .expected = tesSUCCESS},
        // principal 31'536'000 in 2, service fee 1'000'000'000, late fee 0, 1 s late: amount 1'015'768'001
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 1, .amount = 1'015'767'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 1, .amount = 1'015'768'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 1, .amount = 1'015'768'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 1, .amount = 1'015'768'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 1, .amount = 1'015'768'003, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 0, .amount = 1'015'767'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 0, .amount = 1'015'768'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 0, .amount = 1'015'768'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 0, .amount = 1'015'768'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = 0, .amount = 1'015'768'003, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -1, .amount = 1'015'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -1, .amount = 1'015'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -1, .amount = 1'015'768'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -1, .amount = 1'015'768'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -1, .amount = 1'015'768'003, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -2, .amount = 1'015'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -2, .amount = 1'015'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -2, .amount = 1'015'768'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -2, .amount = 1'015'768'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -2, .amount = 1'015'768'003, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -3, .amount = 1'015'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -3, .amount = 1'015'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -3, .amount = 1'015'768'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -3, .amount = 1'015'768'002, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .serviceFee = 1'000'000'000, .due = -3, .amount = 1'015'768'003, .expected = tesSUCCESS},
        // principal 31'536'000 in 2, service fee 0, late fee 1'000'000'000, 1 s late: amount 1'015'768'001
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 1, .amount = 1'015'767'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 1, .amount = 1'015'768'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 1, .amount = 1'015'768'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 1, .amount = 1'015'768'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 1, .amount = 1'015'768'003, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 0, .amount = 1'015'767'999, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 0, .amount = 1'015'768'000, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 0, .amount = 1'015'768'001, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 0, .amount = 1'015'768'002, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = 0, .amount = 1'015'768'003, .expected = tecTOO_SOON},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -1, .amount = 1'015'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -1, .amount = 1'015'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -1, .amount = 1'015'768'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -1, .amount = 1'015'768'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -1, .amount = 1'015'768'003, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -2, .amount = 1'015'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -2, .amount = 1'015'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -2, .amount = 1'015'768'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -2, .amount = 1'015'768'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -2, .amount = 1'015'768'003, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -3, .amount = 1'015'767'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -3, .amount = 1'015'768'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -3, .amount = 1'015'768'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -3, .amount = 1'015'768'002, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 31'536'000, .lateInterestRate = 100'000, .latePaymentFee = 1'000'000'000, .due = -3, .amount = 1'015'768'003, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kServiceFee[] = {
        // installment 1 + service fee 999'999'999
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'997, .amount = 999'999'998, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'997, .amount = 999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'997, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'997, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'997, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'998, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'998, .amount = 999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'998, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'998, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'998, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'999, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'999, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'999, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'999, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 999'999'999, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'000, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'000, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'000, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'000, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'000, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'001, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'001, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'001, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'001, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1'000'000'001, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // installment 999'999'999 + service fee 1
        {.type = PaymentType::regular, .principal = 1'999'999'998, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .amount = 999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 1, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 1, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 1, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 1, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 2, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 2, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 2, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 2, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 2, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 3, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 3, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 3, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 3, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'999'999'998, .serviceFee = 3, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // installment 500'000'000 + service fee 500'000'000
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'998, .amount = 999'999'998, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'998, .amount = 999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'998, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'998, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'998, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'999, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'999, .amount = 999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'999, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'999, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 499'999'999, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'000, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'000, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'000, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'000, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'000, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'001, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'001, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'001, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'001, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'001, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'002, .amount = 999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'002, .amount = 999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'002, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'002, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 1'000'000'000, .serviceFee = 500'000'002, .amount = 1'000'000'002, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kFullPayment[] = {
        // principal 2, close rate 0, close fee 0: amount 2
        {.type = PaymentType::full, .principal = 2, .amount = 1, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .amount = 4, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 1, .amount = 1, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 1, .amount = 2, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 1, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 1, .amount = 4, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 2, .amount = 1, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 2, .amount = 2, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 2, .amount = 3, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 2, .closePaymentFee = 2, .amount = 4, .expected = tesSUCCESS},
        // principal 1'000'000'000, close rate 10'000, close fee 0: amount 1'100'000'000
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .amount = 1'099'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .amount = 1'099'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .amount = 1'100'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .amount = 1'100'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .amount = 1'100'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 1, .amount = 1'099'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 1, .amount = 1'099'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 1, .amount = 1'100'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 1, .amount = 1'100'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 1, .amount = 1'100'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 2, .amount = 1'099'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 2, .amount = 1'099'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 2, .amount = 1'100'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 2, .amount = 1'100'000'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 10'000, .closePaymentFee = 2, .amount = 1'100'000'002, .expected = tesSUCCESS},
        // principal 1'000'000'000, close rate 0, close fee 1'000'000'000: amount 2'000'000'000
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'998, .amount = 1'999'999'998, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'998, .amount = 1'999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'998, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'998, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'998, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'999, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'999, .amount = 1'999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'999, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'999, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 999'999'999, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'000, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'000, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'000, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'000, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'000, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'001, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'001, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'001, .amount = 2'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'001, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'001, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'002, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'002, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'002, .amount = 2'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'002, .amount = 2'000'000'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closePaymentFee = 1'000'000'002, .amount = 2'000'000'002, .expected = tesSUCCESS},
        // principal 1'000'000'000, close rate 100'000, close fee 0: amount 2'000'000'000
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 1, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 1, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 1, .amount = 2'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 1, .amount = 2'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 1, .amount = 2'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 2, .amount = 1'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 2, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 2, .amount = 2'000'000'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 2, .amount = 2'000'000'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 1'000'000'000, .closeInterestRate = 100'000, .closePaymentFee = 2, .amount = 2'000'000'002, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kFullPaymentLastInstallment[] = {
        // principal 6, one installment
        {.type = PaymentType::full, .principal = 6, .paymentTotal = 1, .amount = 6, .expected = tecKILLED},
        {.type = PaymentType::full, .principal = 6, .amount = 6, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 6, .paymentTotal = 3, .amount = 6, .expected = tesSUCCESS},
        // principal 2'000'000'000, one installment
        {.type = PaymentType::full, .principal = 2'000'000'000, .paymentTotal = 1, .amount = 2'000'000'000, .expected = tecKILLED},
        {.type = PaymentType::full, .principal = 2'000'000'000, .amount = 2'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 2'000'000'000, .paymentTotal = 3, .amount = 2'000'000'000, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kFeeRouting[] = {
        // principal 2, rate 1: minimum cover 1
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1, .stage = {.coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1, .stage = {.cover = 1, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1, .stage = {.cover = 2, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2, .serviceFee = 1, .stage = {.cover = 3, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        // principal 2'000'000'000, rate 10'000: minimum cover 200'000'000
        {.type = PaymentType::regular, .principal = 2'000'000'000, .serviceFee = 1, .stage = {.cover = 199'999'998, .coverRate = 10'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .serviceFee = 1, .stage = {.cover = 199'999'999, .coverRate = 10'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .serviceFee = 1, .stage = {.cover = 200'000'000, .coverRate = 10'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .serviceFee = 1, .stage = {.cover = 200'000'001, .coverRate = 10'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'000, .serviceFee = 1, .stage = {.cover = 200'000'002, .coverRate = 10'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        // principal 2'000'000'002, rate 10'000: minimum cover 200'000'001
        {.type = PaymentType::regular, .principal = 2'000'000'002, .serviceFee = 1, .stage = {.cover = 199'999'999, .coverRate = 10'000}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'002, .serviceFee = 1, .stage = {.cover = 200'000'000, .coverRate = 10'000}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'002, .serviceFee = 1, .stage = {.cover = 200'000'001, .coverRate = 10'000}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'002, .serviceFee = 1, .stage = {.cover = 200'000'002, .coverRate = 10'000}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 2'000'000'002, .serviceFee = 1, .stage = {.cover = 200'000'003, .coverRate = 10'000}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // principal 500'000'000, rate 100'000: minimum cover 500'000'000
        {.type = PaymentType::regular, .principal = 500'000'000, .serviceFee = 1, .stage = {.cover = 499'999'998, .coverRate = 100'000}, .amount = 250'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 500'000'000, .serviceFee = 1, .stage = {.cover = 499'999'999, .coverRate = 100'000}, .amount = 250'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 500'000'000, .serviceFee = 1, .stage = {.cover = 500'000'000, .coverRate = 100'000}, .amount = 250'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 500'000'000, .serviceFee = 1, .stage = {.cover = 500'000'001, .coverRate = 100'000}, .amount = 250'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 500'000'000, .serviceFee = 1, .stage = {.cover = 500'000'002, .coverRate = 100'000}, .amount = 250'000'001, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kRegularWithInterest[] = {
        // principal 3'153'600'000 at 100% a year in 2 x 31'536'000 s: installment 4'204'800'000
        {.type = PaymentType::regular, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 4'204'799'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 4'204'799'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 4'204'800'000, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 4'204'800'001, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 4'204'800'002, .expected = tesSUCCESS},
        // principal 3 at the same rate: installment 4
        {.type = PaymentType::regular, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 2, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 3, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::regular, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 4, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 5, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .amount = 6, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kLateWithInterest[] = {
        // installment 4'204'800'000, 1'000 s late at 100% on 3'153'600'000: 100'000 late interest
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -999, .amount = 4'204'899'998, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -999, .amount = 4'204'899'999, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -999, .amount = 4'204'900'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -999, .amount = 4'204'900'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -999, .amount = 4'204'900'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1000, .amount = 4'204'899'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1000, .amount = 4'204'899'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1000, .amount = 4'204'900'000, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1000, .amount = 4'204'900'001, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1000, .amount = 4'204'900'002, .expected = tesSUCCESS},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1001, .amount = 4'204'899'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1001, .amount = 4'204'899'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1001, .amount = 4'204'900'000, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1001, .amount = 4'204'900'001, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::late, .principal = 3'153'600'000, .interestRate = 100'000, .lateInterestRate = 100'000, .paymentInterval = 31'536'000, .due = -1001, .amount = 4'204'900'002, .expected = tecINSUFFICIENT_PAYMENT},
    };
    static constexpr LoanPayCase kFullWithInterest[] = {
        // at the start: principal 3'153'600'000 + close interest 10% 315'360'000
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 3'468'959'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 3'468'959'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 3'468'960'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 3'468'960'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 3'468'960'002, .expected = tesSUCCESS},
        // half an interval in: + accrued interest 1'576'800'000
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .due = 15'768'000, .amount = 5'045'759'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .due = 15'768'000, .amount = 5'045'759'999, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .due = 15'768'000, .amount = 5'045'760'000, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .due = 15'768'000, .amount = 5'045'760'001, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 3'153'600'000, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .due = 15'768'000, .amount = 5'045'760'002, .expected = tesSUCCESS},
        // principal 3 at the start: the close interest 0.3 rounds away, amount due 3
        {.type = PaymentType::full, .principal = 3, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 2, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::full, .principal = 3, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 3, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 3, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 4, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 3, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 5, .expected = tesSUCCESS},
        {.type = PaymentType::full, .principal = 3, .interestRate = 100'000, .closeInterestRate = 10'000, .paymentInterval = 31'536'000, .amount = 6, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kOverpaymentWithInterest[] = {
        // principal 7'000'000'000 at 100% a year in 3 x 31'536'000 s: installment 7'999'999'999
        {.type = PaymentType::overpayment, .principal = 7'000'000'000, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 7'999'999'998, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 7'000'000'000, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 7'999'999'999, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 7'000'000'000, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 8'000'000'000, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 7'000'000'000, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 8'000'000'001, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 7'000'000'000, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 8'000'000'002, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 7'000'000'000, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 9'000'000'000, .expected = tesSUCCESS},
        // principal 7: installment 8
        {.type = PaymentType::overpayment, .principal = 7, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 6, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 7, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 7, .expected = tecINSUFFICIENT_PAYMENT},
        {.type = PaymentType::overpayment, .principal = 7, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 8, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 7, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 9, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 7, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 10, .expected = tesSUCCESS},
        {.type = PaymentType::overpayment, .principal = 7, .interestRate = 100'000, .overpaymentInterestRate = 10'000, .overpaymentFee = 1'000, .paymentInterval = 31'536'000, .paymentTotal = 3, .amount = 12, .expected = tesSUCCESS},
    };
    static constexpr LoanPayCase kCreditBelowGrid[] = {
        // available 20'000'000'000'000'000 units: a credit rounds down to the 10-unit grid
        {.type = PaymentType::regular, .principal = 2, .available = 20'000'000'000'000'000, .amount = 1, .expected = tecPRECISION_LOSS},
        {.type = PaymentType::regular, .principal = 8, .available = 20'000'000'000'000'000, .amount = 4, .expected = tecPRECISION_LOSS},
        {.type = PaymentType::regular, .principal = 10, .available = 20'000'000'000'000'000, .amount = 5, .expected = tecPRECISION_LOSS},
        {.type = PaymentType::regular, .principal = 18, .available = 20'000'000'000'000'000, .amount = 9, .expected = tecPRECISION_LOSS},
        {.type = PaymentType::regular, .principal = 20, .available = 20'000'000'000'000'000, .amount = 10, .expected = tesSUCCESS},
        {.type = PaymentType::regular, .principal = 40, .available = 20'000'000'000'000'000, .amount = 20, .expected = tesSUCCESS},
    };
    // clang-format on
    void
    runLoanPayBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanPayCase const> cases) {
            testcase("LoanPay " + name);
            for (TestLedger const& ledger : ledgers)
            {
                for (std::size_t i = 0; LoanPayCase const& c : cases)
                {
                    jtx::Env& env = *ledger.env;
                    std::uint32_t const parentClose = parentCloseTime(env);
                    LoanParams const p{
                        .principal = units(ledger.f, c.principal),
                        .interestRate = c.interestRate,
                        .lateInterestRate = c.lateInterestRate,
                        .closeInterestRate = c.closeInterestRate,
                        .overpaymentInterestRate = c.overpaymentInterestRate,
                        .overpaymentFee = c.overpaymentFee,
                        .serviceFee = units(ledger.f, c.serviceFee),
                        .latePaymentFee = units(ledger.f, c.latePaymentFee),
                        .closePaymentFee = units(ledger.f, c.closePaymentFee),
                        .paymentInterval = c.paymentInterval,
                        .paymentTotal = c.paymentTotal,
                        .allowsOverpayment = c.type == PaymentType::overpayment,
                    };
                    std::string const at =
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)) +
                        paymentTypeName(c.type) + " of " + std::to_string(c.amount) + " on" +
                        loanText(p) +
                        (c.due ? " due P + " + std::to_string(*c.due) : std::string{}) + " " +
                        stageText(c.stage) +
                        (c.available ? " available " + std::to_string(*c.available)
                                     : std::string{}) +
                        ": ";
                    OpenView view{*env.current()};
                    std::optional<Keylet> loan;
                    if (!tryStage(*this, at, [&] {
                            stageInvestment(env, view, ledger.f, {.managementFeeRate = 1'000});
                            loan = createLoan(env, view, ledger.f, p);
                            if (c.due)
                            {
                                dueAt(view, *loan, parentClose, *c.due);
                            }
                            else
                            {
                                startedAgo(view, *loan, parentClose, 0);
                            }
                            stageLending(env, view, ledger.f, c.stage);
                            if (c.available)
                                stageAvailable(view, ledger.f, *c.available);
                            zeroIouBalance(view, ledger.f.owner, ledger.f.asset.raw());
                        }))
                        continue;
                    Number const amount = units(ledger.f, c.amount);
                    AppliedLoanTx const cpp =
                        applyLoanPay(env, view, ledger.f, *loan, p, c.type, amount);
                    LeanLoanTx const lean = leanLoanPay(cpp, c.type, amount);
                    expectSame(*this, at, cpp, lean, c.expected);
                }
            }
        };

        run("due date", s.all, kDueDate);
        run("late interest", s.all, kLateInterest);
        run("service fee", s.all, kServiceFee);
        run("full payment", s.all, kFullPayment);
        run("full payment of the last installment", s.all, kFullPaymentLastInstallment);
        run("fee routing", s.all, kFeeRouting);
        run("regular with interest", s.all, kRegularWithInterest);
        run("late with interest", s.all, kLateWithInterest);
        run("full with interest", s.all, kFullWithInterest);
        run("overpayment with interest", s.all, kOverpaymentWithInterest);
        run("credit below the vault grid", s.iou, kCreditBelowGrid);
    }

    void
    testLoanPayBoundaries(LendingSetup const& s)
    {
        runLoanPayBoundaries(s);
    }

    // The single-value tests' fixtures: the default broker with 500 of cover, one per asset. Each
    // test runs on a throwaway view of it.
    struct Setup
    {
        BrokerFixture iou;
        BrokerFixture mpt;
    };

    static Setup
    setup(jtx::Env& env, jtx::Env& mptEnv)
    {
        auto const iou = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, iou, Number{500});
        auto const mpt = setUpBrokerVault(
            mptEnv, BrokerConfig{}, Number{10'000}, false, true, LendingAsset::mpt);
        depositCover(mptEnv, mpt, Number{500});
        // Loans are aged by moving their dates back; keep those dates well above zero.
        env.close(env.now() + std::chrono::seconds{10'000});
        mptEnv.close(mptEnv.now() + std::chrono::seconds{10'000});
        return {.iou = iou, .mpt = mpt};
    }

    void
    runTests() override
    {
        jtx::Env env{*this, lendingTestAmendments()};
        jtx::Env mptEnv{*this, lendingTestAmendments()};
        Setup const fx = setup(env, mptEnv);
        BrokerFixture const& iou = fx.iou;
        BrokerFixture const& mpt = fx.mpt;
        jtx::Env iouLendingEnv{*this, lendingTestAmendments()};
        jtx::Env mptLendingEnv{*this, lendingTestAmendments()};
        LendingSetup const s = setUpLending(iouLendingEnv, mptLendingEnv);

        struct PayTest
        {
            char const* name;
            LoanParams loan{};
            std::uint32_t loanAge{};
            PaymentType type = PaymentType::regular;
            Number amount;
            TER expected;
            LoanKind kind = LoanKind::active;
        };
        auto const pay = [&](jtx::Env& e, BrokerFixture const& f, PayTest const& t) {
            runPay(e, f, t.name, t.loan, t.loanAge, t.type, t.amount, t.expected, t.kind);
        };

        // clang-format off
        // Regular payments on a 1000 loan in two installments of 500 (no interest).
        static PayTest const kRegularTests[] = {
            {.name = "one installment", .amount = 500, .expected = tesSUCCESS},
            {.name = "both installments in one transaction", .amount = 1'000, .expected = tesSUCCESS},
            {.name = "amount below one installment", .amount = 499, .expected = tecINSUFFICIENT_PAYMENT},
            {.name = "one installment with interest", .loan = {.interestRate = 10'000, .paymentTotal = 3}, .amount = 400, .expected = tesSUCCESS},
            {.name = "one installment with a service fee", .loan = {.serviceFee = Number{1}}, .amount = 501, .expected = tesSUCCESS},
            {.name = "when late", .loanAge = 601, .amount = 500, .expected = tecEXPIRED},
            {.name = "on a pending proposal", .amount = 500, .expected = tecNO_PERMISSION, .kind = LoanKind::pending},
            {.name = "on a paid-off loan", .amount = 500, .expected = tecKILLED, .kind = LoanKind::paidOff},
        };
        // clang-format on
        for (PayTest const& t : kRegularTests)
            pay(env, iou, t);
        testTwoInstallments(env, iou);

        // Late payments
        // clang-format off
        static PayTest const kLateTests[] = {
            {.name = "one installment", .loan = {.lateInterestRate = 10'000, .latePaymentFee = Number{2}}, .loanAge = 601, .type = PaymentType::late, .amount = 600, .expected = tesSUCCESS},
            {.name = "before the due date", .type = PaymentType::late, .amount = 600, .expected = tecTOO_SOON},
            {.name = "without a late rate or fee", .loanAge = 601, .type = PaymentType::late, .amount = 500, .expected = tesSUCCESS},
            {.name = "amount below the installment", .loanAge = 601, .type = PaymentType::late, .amount = 100, .expected = tecINSUFFICIENT_PAYMENT},
        };
        // clang-format on
        for (PayTest const& t : kLateTests)
            pay(env, iou, t);
        testPayImpairedLoan(env, iou);

        // clang-format off
        static PayTest const kInstallmentCapAndFullTests[] = {
            // One transaction settles at most 100 installments.
            {.name = "stops at 100 installments", .loan = {.principal = Number{1'500}, .paymentTotal = 150}, .amount = 1'500, .expected = tesSUCCESS},
            {.name = "stops at 100 installments", .loan = {.principal = Number{1'500}, .paymentTotal = 150, .allowsOverpayment = true}, .type = PaymentType::overpayment, .amount = 1'500, .expected = tesSUCCESS},
            // Full payments
            {.name = "below the amount due", .loan = {.interestRate = 10'000, .paymentTotal = 3}, .loanAge = 100, .type = PaymentType::full, .amount = 900, .expected = tecINSUFFICIENT_PAYMENT},
            {.name = "pay off a three-installment loan", .loan = {.interestRate = 10'000, .closeInterestRate = 1'000, .paymentTotal = 3}, .loanAge = 100, .type = PaymentType::full, .amount = 1'100, .expected = tesSUCCESS},
            {.name = "without a close rate", .loan = {.interestRate = 10'000, .paymentTotal = 3}, .loanAge = 100, .type = PaymentType::full, .amount = 1'100, .expected = tesSUCCESS},
            {.name = "when late", .loan = {.interestRate = 10'000, .paymentTotal = 3}, .loanAge = 601, .type = PaymentType::full, .amount = 1'100, .expected = tecEXPIRED},
            {.name = "on a zero-interest loan", .loan = {.paymentTotal = 3}, .loanAge = 100, .type = PaymentType::full, .amount = 1'000, .expected = tesSUCCESS},
        };
        // clang-format on
        for (PayTest const& t : kInstallmentCapAndFullTests)
            pay(env, iou, t);
        testFullAfterInstallment(env, iou, false);
        testFullAfterInstallment(env, iou, true);
        // clang-format off
        pay(env, iou, {.name = "with one installment left", .loan = {.paymentTotal = 1}, .type = PaymentType::full, .amount = 1'100, .expected = tecKILLED});
        // clang-format on

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
                .allowsOverpayment = true,
            },
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
                .allowsOverpayment = true,
            },
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
                .allowsOverpayment = true,
            },
            9'451,
            {Number{3'117'013'163'787'732LL, -14}});

        // MPT vault
        // clang-format off
        static PayTest const kMptTests[] = {
            {.name = "one installment with interest", .loan = {.interestRate = 10'000, .paymentTotal = 3}, .amount = 400, .expected = tesSUCCESS},
            {.name = "one installment", .loan = {.lateInterestRate = 10'000, .latePaymentFee = Number{2}}, .loanAge = 601, .type = PaymentType::late, .amount = 600, .expected = tesSUCCESS},
            {.name = "pay off a three-installment loan", .loan = {.interestRate = 10'000, .closeInterestRate = 1'000, .paymentTotal = 3}, .loanAge = 100, .type = PaymentType::full, .amount = 1'100, .expected = tesSUCCESS},
        };
        // clang-format on
        for (PayTest const& t : kMptTests)
            pay(mptEnv, mpt, t);

        // Overpayments
        // clang-format off
        static PayTest const kOverpaymentTests[] = {
            {.name = "amount clears the whole loan", .loan = {.interestRate = 10'000, .paymentTotal = 3, .allowsOverpayment = true}, .type = PaymentType::overpayment, .amount = 1'200, .expected = tesSUCCESS},
            {.name = "extra below one grid unit", .loan = {.allowsOverpayment = true}, .type = PaymentType::overpayment, .amount = Number{5'000'000'005LL, -7}, .expected = tesSUCCESS},
            // A 100% overpayment fee consumes the extra, so no principal is paid down.
            {.name = "extra consumed by the overpayment fee", .loan = {.overpaymentFee = 100'000, .paymentTotal = 3, .allowsOverpayment = true}, .type = PaymentType::overpayment, .amount = 600, .expected = tesSUCCESS},
            {.name = "one installment plus extra principal", .loan = {.interestRate = 10'000, .overpaymentInterestRate = 1'000, .overpaymentFee = 500, .paymentTotal = 4, .allowsOverpayment = true}, .type = PaymentType::overpayment, .amount = 500, .expected = tesSUCCESS},
            {.name = "on a loan that forbids it", .type = PaymentType::overpayment, .amount = 600, .expected = tecNO_PERMISSION},
        };
        // clang-format on
        for (PayTest const& t : kOverpaymentTests)
            pay(env, iou, t);
        testLoanPayBoundaries(s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanPay, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
