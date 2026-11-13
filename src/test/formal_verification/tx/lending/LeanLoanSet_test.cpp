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
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// A LoanSet on a broker staged as `stage` (vault grid units), with the vault in its investment
// phase unless `subscription` and `redemption` set its dates (offsets from the parent close time
// P). A start date, as an offset from P or as `startAt`, makes it a two-step proposal. A C++
// preflight rejection (tem) is paired with `leanError`, the model error that stands for it.
struct LoanSetCase
{
    LendingStage stage{};
    std::optional<std::int64_t> subscription{};
    std::optional<std::int64_t> redemption{};
    std::int64_t principal{};
    // The principal is principal * 10^principalExponent vault grid units.
    int principalExponent{};
    std::int64_t originationFee{};
    std::int64_t serviceFee{};
    std::int64_t latePaymentFee{};
    std::int64_t closePaymentFee{};
    // Each fee is fee * 10^feeExponent vault grid units.
    int feeExponent{};
    std::uint32_t interestRate{};
    std::uint32_t paymentInterval{600};
    std::uint32_t paymentTotal{1};
    std::optional<std::uint32_t> gracePeriod{};
    std::optional<std::int64_t> start{};
    std::optional<std::uint32_t> startAt{};
    TER expected;
    std::optional<LeanError> leanError{};
};

// A LoanAccept of a one-payment proposal of `principal` units starting 1'000 s after the parent
// close time P, made with the vault in its investment phase. Then `stage` is staged and, when set,
// the proposal's start date (its next due date follows) and the vault's dates are restaged as
// offsets from P.
struct LoanAcceptCase
{
    LendingStage stage{};
    std::int64_t principal{};
    std::uint32_t interestRate{};
    std::uint32_t paymentInterval{600};
    std::optional<std::int64_t> start{};
    std::optional<std::int64_t> subscription{};
    std::optional<std::int64_t> redemption{};
    TER expected;
};

enum class DeleteParty : std::uint8_t { Borrower, Owner, Other };

// A LoanDelete by the borrower (or `by`) of a loan of `principal` units in `paymentTotal`
// installments 600 s apart, taken with the vault in its investment phase after a `debt`-unit loan:
// a proposal starting 1'000 s after P when `pending`, else an active loan with `paid` installments
// paid, then impaired while due at P - 1 when `impaired`, then defaulted past its grace period when
// `defaulted`.
struct LoanDeleteCase
{
    std::int64_t debt{};
    std::int64_t principal{};
    std::uint32_t interestRate{};
    std::uint32_t paymentTotal{};
    std::uint32_t paid{};
    TER expected;
    bool pending{};
    bool defaulted{};
    DeleteParty by{};
    bool impaired{};
};

// Differential tests of LoanSet (one-step and two-step), LoanAccept and LoanDelete. Each case
// compares the model's preclaim TER, then (when preclaim accepts) its doApply TER and the loan,
// vault and broker post-states.
// Rows stage ledger state on a throwaway view, including states no transaction sequence may
// reach: a verdict compares model and C++ on the same pre-state, not a claim the state is
// reachable (see stageLending).
class LeanLoanSet_test : public LeanSuite
{
    // LoanSet for `p` on `view` (already staged) and in the model on the same pre-state.
    void
    checkLoanSet(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        LoanParams const& p,
        TER expected,
        std::optional<LeanError> leanError,
        std::string const& at)
    {
        zeroIouBalance(view, f.borrower, f.asset.raw());
        zeroIouBalance(view, f.owner, f.asset.raw());
        AppliedLoanTx const cpp = applyLoanSet(env, view, f, p);
        LeanLoanTx const lean = leanLoanSet(cpp, p);
        expectRow(*this, at, cpp, lean, expected, leanError);
    }

    // Stage `s` on a throwaway view of `env`, then check the LoanSet there.
    void
    checkLoanSet(
        jtx::Env& env,
        BrokerFixture const& f,
        LendingStage const& s,
        LoanParams const& p,
        TER expected)
    {
        std::string const at = stageText(s) + loanText(p) + ": ";
        OpenView view{*env.current()};
        if (!tryStage(*this, at, [&] { stageLending(env, view, f, s); }))
            return;
        checkLoanSet(env, f, view, p, expected, std::nullopt, at);
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
        std::uint32_t const parentClose = view.parentCloseTime().time_since_epoch().count();
        std::uint32_t sub = parentClose - 30;
        if (!toInvestment)
            sub = parentClose + 600;
        if (toRedemption)
            sub = parentClose - 1'000'001;
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
        LendingSetup const& s,
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
        TestLedger const& l = assetKind == LendingAsset::mpt ? s.mptLedger : s.iouLedger;
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
    runTwoStep(
        LendingSetup const& s,
        std::string const& label,
        std::int64_t startOffset,
        TER expected)
    {
        testcase("LoanSet: " + label);
        TestLedger const& l = s.iouLedger;
        std::uint32_t const parentClose = parentCloseTime(*l.env);
        checkLoanSet(
            *l.env,
            l.f,
            singleValueStage(*l.env->current(), l.f, Number{500}, std::nullopt, true, false),
            LoanParams{.startDate = static_cast<std::uint32_t>(parentClose + startOffset)},
            expected);
    }

    // LoanAccept of the pending loan at `loanKeylet` on `view` and in the model.
    void
    checkAccept(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        Keylet const& loanKeylet,
        LoanParams const& p,
        TER expected,
        std::string const& at)
    {
        zeroIouBalance(view, f.borrower, f.asset.raw());
        zeroIouBalance(view, f.owner, f.asset.raw());
        AppliedLoanTx const cpp = applyLoanAccept(env, view, f, loanKeylet, p);
        LeanLoanTx const lean = leanLoanAccept(cpp);
        expectSame(*this, at, cpp, lean, expected);
    }

    // A pending proposal starting `startOffset` seconds from now, accepted after advancing the
    // ledger `acceptAfter` seconds (0 = right away).
    void
    runAccept(
        std::string const& label,
        bool pending,
        std::uint32_t acceptAfter,
        TER expected,
        Number originationFee = Number{0})
    {
        using namespace jtx;
        testcase("LoanAccept: " + label);

        Env env{*this, lendingTestAmendments()};
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams p{.originationFee = originationFee};
        if (pending)
            p.startDate = parentCloseTime(env) + 1'000;
        auto const loanKeylet = submitLoanSet(env, f, p);
        if (acceptAfter != 0)
            closeAt(env, parentCloseTime(env) + acceptAfter);
        OpenView view{*env.current()};
        checkAccept(env, f, view, loanKeylet, p, expected, label + ": ");
    }

    // The vault sits at its open limit, so the interest of a new loan does not fit.
    void
    testLoanInterestPastOpenLimit()
    {
        using namespace jtx;
        testcase("LoanSet: loan interest past the vault's open limit");

        Env env{*this, lendingTestAmendments()};
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

        Env env{*this, lendingTestAmendments()};
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
        checkAccept(env, f, view, loanKeylet, p, tecLIMIT_EXCEEDED, "past the open limit: ");
    }

    // Late interest paid on a loan of most of a vault at its open limit pushes the vault's total
    // past 16 digits, coarsening its live scale; a coarsened vault refuses new loans.
    void
    testCoarsenedVaultRefusesLoan()
    {
        using namespace jtx;
        testcase("LoanSet: coarsened vault refuses a loan");

        Env env{*this, lendingTestAmendments()};
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
    void
    testLoanSetAtPhaseBoundary(bool atRedemption)
    {
        using namespace jtx;
        testcase(
            std::string("LoanSet: exactly at the ") +
            (atRedemption ? "redemption" : "subscription") + " date");

        Env env{*this, lendingTestAmendments()};
        auto const f = setUpBrokerVault(env, BrokerConfig{}, Number{10'000}, false, false);
        depositCover(env, f, Number{500});
        BEAST_EXPECTS(
            closeExactlyAt(env, atRedemption ? f.redemptionDate : f.subscriptionDate),
            "the parent close time missed the schedule date");
        checkLoanSet(env, f, {}, LoanParams{}, atRedemption ? tecEXPIRED : tecTOO_SOON);
    }

    // A proposal expires at its start date, judged at the parent close time.
    void
    testAcceptAtStartDate()
    {
        using namespace jtx;
        testcase("LoanAccept: exactly at the start date");

        Env env{*this, lendingTestAmendments()};
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        NetClock::time_point const start = alignedTime(
            env, NetClock::time_point{NetClock::duration{parentCloseTime(env) + 1'000}});
        LoanParams p;
        p.startDate = timeCount(start);
        auto const loanKeylet = submitLoanSet(env, f, p);
        BEAST_EXPECTS(closeExactlyAt(env, start), "the parent close time missed the start date");
        OpenView view{*env.current()};
        checkAccept(env, f, view, loanKeylet, p, tecEXPIRED, "at the start date: ");
    }

    // Each row stages the asset's shared ledger on a throwaway view (the vault in its investment
    // phase unless the row sets its dates), applies the transaction there and expects its verdict
    // on both sides, with every field of the loan, its broker and the pool, and the amount sent to
    // the borrower, equal when both succeed. Amounts are in units of the vault grid; loans have one
    // payment 600 s apart unless the row says otherwise.
    // A group comment names a boundary value (the cusp); its rows step those values around it.
    // LoanSet:
    // - Debt maximum: debt + principal above the broker's debt maximum is tecLIMIT_EXCEEDED. Each
    //   cusp puts it exactly on the maximum; with interest (100% over 3'153'600 s, interest
    //   ceil(principal / 10)) the cusp stays put, as the debt counts the principal only.
    // - Assets available: a principal above the vault's available assets (1e10 less the debt) is
    //   tecINSUFFICIENT_FUNDS.
    // - Cover at origination: cover below ceil((debt + principal) * rate / 1e5) is
    //   tecINSUFFICIENT_FUNDS. Each cusp deposits exactly that cover.
    // - Payment count: a zero-interest loan with installments 60 s apart is tecPRECISION_LOSS
    //   unless principal > (payments - 1) * ceil(principal / payments), in grid units for either
    //   asset.
    // - Redemption buffer (IOU): the last payment of a two-step loan starting at P + 1'000 must
    //   fall 60 s before the vault's redemption date, else tecNO_PERMISSION.
    // - Open zone: a loan whose interest takes assets total + yield + ceil(principal / 10) past
    //   the open limit (9e15 units) is tecLIMIT_EXCEEDED. Each cusp lands exactly on it.
    // - Grid: a principal or fee off the vault grid is tecPRECISION_LOSS (for an MPT, a fractional
    //   amount). Each cusp is one step of 10^level units with a 16-digit mantissa; fees ride on a
    //   2e9-unit loan.
    // - Subscription date (IOU): a LoanSet at or before the vault's subscription date is
    //   tecTOO_SOON.
    // - Redemption date (IOU): at or after the redemption date tecEXPIRED; just before it the
    //   schedule no longer fits (tecNO_PERMISSION).
    // - Start date (IOU): a two-step proposal starting at or before P is tecEXPIRED.
    // - Origination fee: a fee above the principal or below zero is temINVALID (the model: not
    //   lawful, the fix of model gap 2). Each cusp puts the fee exactly on the principal.
    // - Principal and payments: a principal of zero or less, or zero payments, is temINVALID in
    //   C++; the model does not answer notLawful there (rows kept out, model gap 18). The valid
    //   neighbours (principal 1 unit, one payment) run, one-step and two-step.
    // - Cap (MPT): a principal or fee above 2^63 - 1 is tecPRECISION_LOSS (the largest 16-digit
    //   mantissa at exponent 3 under the cap; a principal under it is above the vault's assets).
    // - Fee minimum: a negative service, late or close fee is temINVALID (not lawful).
    // - Protocol time limit (IOU): a schedule whose last grace period ends past 2^32 - 1 is
    //   tecKILLED, checked first. Below it the proposal fails the redemption buffer or, starting at
    //   0, has expired.
    // LoanAccept (of a proposal starting at P + 1'000, then restaged):
    // - Start date (IOU): accepting a proposal whose start date is at or before P is tecEXPIRED.
    // - Subscription date (IOU): a vault at or before its subscription date is tecTOO_SOON.
    // - Redemption date (IOU): a vault at or past its redemption date is tecEXPIRED (LoanAccept
    //   does not re-check the redemption buffer).
    // - Open zone: the LoanSet open zone rows, with the yield staged after the proposal.
    // LoanDelete (the loan gone, and every broker and pool field equal, when both succeed):
    // - Payments remaining: an active loan with payments remaining is tecHAS_OBLIGATIONS; a
    //   paid-off or defaulted loan, or a proposal, is deleted.
    // - Beside another loan: the broker keeps the other loan's debt.
    // - Party: only the broker owner or the borrower may delete (tecNO_PERMISSION), checked after
    //   the obligations.
    // - Impaired: an impaired loan still has payments remaining (tecHAS_OBLIGATIONS) until it is
    //   defaulted. A missing loan (tecNO_ENTRY) is outside the model, which deletes a given loan.
    // clang-format off
    static constexpr LoanSetCase kDebtMaximum[] = {
        // debt 1 + principal 1 = maximum 2
        {.stage = {.debtMaximum = 2}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 2}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 2}, .principal = 3, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 2}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 2}, .principal = 2, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 2}, .principal = 3, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 2}, .principal = 1, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 2}, .principal = 2, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 2}, .principal = 3, .expected = tecLIMIT_EXCEEDED},
        // debt 1 + principal 999'999'999 = maximum 1'000'000'000
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 999'999'997, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 999'999'997, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 999'999'997, .expected = tesSUCCESS},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 999'999'997, .expected = tesSUCCESS},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        // debt 999'999'999 + principal 1 = maximum 1'000'000'000
        {.stage = {.debt = 999'999'997, .debtMaximum = 1'000'000'000}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'997, .debtMaximum = 1'000'000'000}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'997, .debtMaximum = 1'000'000'000}, .principal = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998, .debtMaximum = 1'000'000'000}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998, .debtMaximum = 1'000'000'000}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998, .debtMaximum = 1'000'000'000}, .principal = 3, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 999'999'999, .debtMaximum = 1'000'000'000}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .debtMaximum = 1'000'000'000}, .principal = 2, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 999'999'999, .debtMaximum = 1'000'000'000}, .principal = 3, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000, .debtMaximum = 1'000'000'000}, .principal = 1, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000, .debtMaximum = 1'000'000'000}, .principal = 2, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000, .debtMaximum = 1'000'000'000}, .principal = 3, .expected = tecLIMIT_EXCEEDED},
        // debt 500'000'000 + principal 500'000'000 = maximum 1'000'000'000
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr LoanSetCase kDebtMaximumWithInterest[] = {
        // debt 1 + principal 1 = maximum 2
        {.stage = {.debtMaximum = 2}, .principal = 1, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 2}, .principal = 2, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 2}, .principal = 3, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 2}, .principal = 1, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 2}, .principal = 2, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 2}, .principal = 3, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 2}, .principal = 1, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 2}, .principal = 2, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 2}, .principal = 3, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        // debt 1 + principal 999'999'999 = maximum 1'000'000'000
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 999'999'997, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 999'999'997, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 999'999'997, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 999'999'997, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3, .debtMaximum = 1'000'000'000}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        // debt 999'999'999 + principal 1 = maximum 1'000'000'000
        {.stage = {.debt = 999'999'997, .debtMaximum = 1'000'000'000}, .principal = 1, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'997, .debtMaximum = 1'000'000'000}, .principal = 2, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'997, .debtMaximum = 1'000'000'000}, .principal = 3, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998, .debtMaximum = 1'000'000'000}, .principal = 1, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998, .debtMaximum = 1'000'000'000}, .principal = 2, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998, .debtMaximum = 1'000'000'000}, .principal = 3, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 999'999'999, .debtMaximum = 1'000'000'000}, .principal = 1, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .debtMaximum = 1'000'000'000}, .principal = 2, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 999'999'999, .debtMaximum = 1'000'000'000}, .principal = 3, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000, .debtMaximum = 1'000'000'000}, .principal = 1, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000, .debtMaximum = 1'000'000'000}, .principal = 2, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000, .debtMaximum = 1'000'000'000}, .principal = 3, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        // debt 500'000'000 + principal 500'000'000 = maximum 1'000'000'000
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'998, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 499'999'999, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'000, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'001, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 499'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 499'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 500'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 500'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 500'000'002, .debtMaximum = 1'000'000'000}, .principal = 500'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr LoanSetCase kAssetsAvailable[] = {
        // debt 0 + principal 10'000'000'000 = assets 10'000'000'000
        {.principal = 9'999'999'998, .expected = tesSUCCESS},
        {.principal = 9'999'999'999, .expected = tesSUCCESS},
        {.principal = 10'000'000'000, .expected = tesSUCCESS},
        {.principal = 10'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.principal = 10'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1}, .principal = 9'999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1}, .principal = 9'999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1}, .principal = 10'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1}, .principal = 10'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1}, .principal = 10'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2}, .principal = 9'999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 2}, .principal = 9'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2}, .principal = 10'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2}, .principal = 10'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2}, .principal = 10'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        // debt 9'999'999'999 + principal 1 = assets 10'000'000'000
        {.stage = {.debt = 9'999'999'997}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 9'999'999'997}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 9'999'999'997}, .principal = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 9'999'999'998}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 9'999'999'998}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 9'999'999'998}, .principal = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'999'999'999}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 9'999'999'999}, .principal = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'999'999'999}, .principal = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 10'000'000'000}, .principal = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 10'000'000'000}, .principal = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 10'000'000'000}, .principal = 3, .expected = tecINSUFFICIENT_FUNDS},
        // debt 9'000'000'000 + principal 1'000'000'000 = assets 10'000'000'000
        {.stage = {.debt = 8'999'999'998}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'998}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'998}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'998}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'998}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'999}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'999}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'999}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'999}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 8'999'999'999}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 9'000'000'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 9'000'000'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 9'000'000'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'001}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 9'000'000'001}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 9'000'000'001}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'001}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'001}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'002}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 9'000'000'002}, .principal = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'002}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'002}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 9'000'000'002}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        // debt 5'000'000'000 + principal 5'000'000'000 = assets 10'000'000'000
        {.stage = {.debt = 4'999'999'998}, .principal = 4'999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'998}, .principal = 4'999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'998}, .principal = 5'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'998}, .principal = 5'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'998}, .principal = 5'000'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'999}, .principal = 4'999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'999}, .principal = 4'999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'999}, .principal = 5'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'999}, .principal = 5'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 4'999'999'999}, .principal = 5'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'000}, .principal = 4'999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 5'000'000'000}, .principal = 4'999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 5'000'000'000}, .principal = 5'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 5'000'000'000}, .principal = 5'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'000}, .principal = 5'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'001}, .principal = 4'999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 5'000'000'001}, .principal = 4'999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 5'000'000'001}, .principal = 5'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'001}, .principal = 5'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'001}, .principal = 5'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'002}, .principal = 4'999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 5'000'000'002}, .principal = 4'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'002}, .principal = 5'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'002}, .principal = 5'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 5'000'000'002}, .principal = 5'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
    };
    static constexpr LoanSetCase kOriginationCover[] = {
        // debt 0, principal 1, rate 1: cover 1
        {.stage = {.coverRate = 1}, .principal = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.coverRate = 1}, .principal = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.coverRate = 1}, .principal = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 3, .expected = tesSUCCESS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 3, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 2, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 3, .expected = tesSUCCESS},
        // debt 0, principal 100'000, rate 1: cover 1
        {.stage = {.coverRate = 1}, .principal = 99'998, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.coverRate = 1}, .principal = 99'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.coverRate = 1}, .principal = 100'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.coverRate = 1}, .principal = 100'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.coverRate = 1}, .principal = 100'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 99'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 99'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 100'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 100'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1, .coverRate = 1}, .principal = 100'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 99'998, .expected = tesSUCCESS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 99'999, .expected = tesSUCCESS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 100'000, .expected = tesSUCCESS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 100'001, .expected = tesSUCCESS},
        {.stage = {.cover = 2, .coverRate = 1}, .principal = 100'002, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 99'998, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 99'999, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 100'000, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 100'001, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .principal = 100'002, .expected = tesSUCCESS},
        // debt 0, principal 1'000'000'000, rate 10'000: cover 100'000'000
        {.stage = {.cover = 99'999'998, .coverRate = 10'000}, .principal = 999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'998, .coverRate = 10'000}, .principal = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'998, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'998, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'998, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        // debt 0, principal 1'000'000'001, rate 10'000: cover 100'000'001
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 99'999'999, .coverRate = 10'000}, .principal = 1'000'000'003, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 100'000'000, .coverRate = 10'000}, .principal = 1'000'000'003, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'001, .coverRate = 10'000}, .principal = 1'000'000'003, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'002, .coverRate = 10'000}, .principal = 1'000'000'003, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'003, .coverRate = 10'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'003, .coverRate = 10'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'003, .coverRate = 10'000}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'003, .coverRate = 10'000}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.cover = 100'000'003, .coverRate = 10'000}, .principal = 1'000'000'003, .expected = tesSUCCESS},
        // debt 1'000'000'000, principal 1'000'000'000, rate 1: cover 20'000
        {.stage = {.debt = 1'000'000'000, .cover = 19'998, .coverRate = 1}, .principal = 999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'998, .coverRate = 1}, .principal = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'998, .coverRate = 1}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'998, .coverRate = 1}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'998, .coverRate = 1}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'999, .coverRate = 1}, .principal = 999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'999, .coverRate = 1}, .principal = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'999, .coverRate = 1}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'999, .coverRate = 1}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 19'999, .coverRate = 1}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'000, .coverRate = 1}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'000, .coverRate = 1}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'000, .coverRate = 1}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'000, .coverRate = 1}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'000, .coverRate = 1}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'001, .coverRate = 1}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'001, .coverRate = 1}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'001, .coverRate = 1}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'001, .coverRate = 1}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'001, .coverRate = 1}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'002, .coverRate = 1}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'002, .coverRate = 1}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'002, .coverRate = 1}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'002, .coverRate = 1}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 20'002, .coverRate = 1}, .principal = 1'000'000'002, .expected = tesSUCCESS},
        // debt 0, principal 1'000'000'000, rate 100'000: cover 1'000'000'000
        {.stage = {.cover = 999'999'998, .coverRate = 100'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998, .coverRate = 100'000}, .principal = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'998, .coverRate = 100'000}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'998, .coverRate = 100'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'998, .coverRate = 100'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'999, .coverRate = 100'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999, .coverRate = 100'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999, .coverRate = 100'000}, .principal = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'999, .coverRate = 100'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'999, .coverRate = 100'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'000, .coverRate = 100'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000, .coverRate = 100'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000, .coverRate = 100'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000, .coverRate = 100'000}, .principal = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'000, .coverRate = 100'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'001, .coverRate = 100'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001, .coverRate = 100'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001, .coverRate = 100'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001, .coverRate = 100'000}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001, .coverRate = 100'000}, .principal = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'002, .coverRate = 100'000}, .principal = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002, .coverRate = 100'000}, .principal = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002, .coverRate = 100'000}, .principal = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002, .coverRate = 100'000}, .principal = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002, .coverRate = 100'000}, .principal = 1'000'000'002, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kPaymentCount[] = {
        // count 2, principal 2
        {.principal = 1, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 1, .paymentInterval = 60, .paymentTotal = 2, .expected = tecPRECISION_LOSS},
        {.principal = 1, .paymentInterval = 60, .paymentTotal = 3, .expected = tecPRECISION_LOSS},
        {.principal = 1, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 2, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 2, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 2, .paymentInterval = 60, .paymentTotal = 3, .expected = tecPRECISION_LOSS},
        {.principal = 2, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 3, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 3, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 4, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 3, .expected = tecPRECISION_LOSS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 4, .expected = tesSUCCESS},
        // count 3, principal 3
        {.principal = 1, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 1, .paymentInterval = 60, .paymentTotal = 2, .expected = tecPRECISION_LOSS},
        {.principal = 1, .paymentInterval = 60, .paymentTotal = 3, .expected = tecPRECISION_LOSS},
        {.principal = 1, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 1, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        {.principal = 2, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 2, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 2, .paymentInterval = 60, .paymentTotal = 3, .expected = tecPRECISION_LOSS},
        {.principal = 2, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 2, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        {.principal = 3, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 3, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        {.principal = 4, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 3, .expected = tecPRECISION_LOSS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 4, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        {.principal = 5, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 3, .expected = tesSUCCESS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 5, .expected = tesSUCCESS},
        // count 3, principal 5
        {.principal = 3, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 3, .expected = tesSUCCESS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 3, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        {.principal = 4, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 3, .expected = tecPRECISION_LOSS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 4, .expected = tesSUCCESS},
        {.principal = 4, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        {.principal = 5, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 3, .expected = tesSUCCESS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 5, .paymentInterval = 60, .paymentTotal = 5, .expected = tesSUCCESS},
        {.principal = 6, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 6, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 6, .paymentInterval = 60, .paymentTotal = 3, .expected = tesSUCCESS},
        {.principal = 6, .paymentInterval = 60, .paymentTotal = 4, .expected = tecPRECISION_LOSS},
        {.principal = 6, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        {.principal = 7, .paymentInterval = 60, .expected = tesSUCCESS},
        {.principal = 7, .paymentInterval = 60, .paymentTotal = 2, .expected = tesSUCCESS},
        {.principal = 7, .paymentInterval = 60, .paymentTotal = 3, .expected = tesSUCCESS},
        {.principal = 7, .paymentInterval = 60, .paymentTotal = 4, .expected = tesSUCCESS},
        {.principal = 7, .paymentInterval = 60, .paymentTotal = 5, .expected = tecPRECISION_LOSS},
        // count 100, principal 100
        {.principal = 98, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 98, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 98, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 98, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 98, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 99, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 99, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 99, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 99, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 99, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 100, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 100, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 100, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 100, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 100, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 101, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 101, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 101, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 101, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 101, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 102, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 102, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 102, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 102, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 102, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        // count 100, principal 4'951
        {.principal = 4'949, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 4'949, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 4'949, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 4'949, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 4'949, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 4'950, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 4'950, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 4'950, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 4'950, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 4'950, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 4'951, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 4'951, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 4'951, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 4'951, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 4'951, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 4'952, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 4'952, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 4'952, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 4'952, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 4'952, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 4'953, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 4'953, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 4'953, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 4'953, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 4'953, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        // count 100, principal 5'000
        {.principal = 4'998, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 4'998, .paymentInterval = 60, .paymentTotal = 99, .expected = tecPRECISION_LOSS},
        {.principal = 4'998, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 4'998, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 4'998, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 4'999, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 4'999, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 4'999, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 4'999, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 4'999, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 5'000, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 5'000, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 5'000, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 5'000, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 5'000, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 5'001, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 5'001, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 5'001, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 5'001, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 5'001, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        {.principal = 5'002, .paymentInterval = 60, .paymentTotal = 98, .expected = tecPRECISION_LOSS},
        {.principal = 5'002, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 5'002, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 5'002, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 5'002, .paymentInterval = 60, .paymentTotal = 102, .expected = tecPRECISION_LOSS},
        // count 100, principal 9'802
        {.principal = 9'800, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 9'800, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 9'800, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 9'800, .paymentInterval = 60, .paymentTotal = 101, .expected = tecPRECISION_LOSS},
        {.principal = 9'800, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 9'801, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 9'801, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 9'801, .paymentInterval = 60, .paymentTotal = 100, .expected = tecPRECISION_LOSS},
        {.principal = 9'801, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 9'801, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 9'802, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 9'802, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 9'802, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 9'802, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 9'802, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 9'803, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 9'803, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 9'803, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 9'803, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 9'803, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        {.principal = 9'804, .paymentInterval = 60, .paymentTotal = 98, .expected = tesSUCCESS},
        {.principal = 9'804, .paymentInterval = 60, .paymentTotal = 99, .expected = tesSUCCESS},
        {.principal = 9'804, .paymentInterval = 60, .paymentTotal = 100, .expected = tesSUCCESS},
        {.principal = 9'804, .paymentInterval = 60, .paymentTotal = 101, .expected = tesSUCCESS},
        {.principal = 9'804, .paymentInterval = 60, .paymentTotal = 102, .expected = tesSUCCESS},
        // count 31'623, principal 999'950'885
        {.principal = 999'950'883, .paymentInterval = 60, .paymentTotal = 31'621, .expected = tesSUCCESS},
        {.principal = 999'950'883, .paymentInterval = 60, .paymentTotal = 31'622, .expected = tesSUCCESS},
        {.principal = 999'950'883, .paymentInterval = 60, .paymentTotal = 31'623, .expected = tesSUCCESS},
        {.principal = 999'950'883, .paymentInterval = 60, .paymentTotal = 31'624, .expected = tecPRECISION_LOSS},
        {.principal = 999'950'883, .paymentInterval = 60, .paymentTotal = 31'625, .expected = tesSUCCESS},
        {.principal = 999'950'884, .paymentInterval = 60, .paymentTotal = 31'621, .expected = tesSUCCESS},
        {.principal = 999'950'884, .paymentInterval = 60, .paymentTotal = 31'622, .expected = tesSUCCESS},
        {.principal = 999'950'884, .paymentInterval = 60, .paymentTotal = 31'623, .expected = tecPRECISION_LOSS},
        {.principal = 999'950'884, .paymentInterval = 60, .paymentTotal = 31'624, .expected = tesSUCCESS},
        {.principal = 999'950'884, .paymentInterval = 60, .paymentTotal = 31'625, .expected = tesSUCCESS},
        {.principal = 999'950'885, .paymentInterval = 60, .paymentTotal = 31'621, .expected = tesSUCCESS},
        {.principal = 999'950'885, .paymentInterval = 60, .paymentTotal = 31'622, .expected = tesSUCCESS},
        {.principal = 999'950'885, .paymentInterval = 60, .paymentTotal = 31'623, .expected = tesSUCCESS},
        {.principal = 999'950'885, .paymentInterval = 60, .paymentTotal = 31'624, .expected = tesSUCCESS},
        {.principal = 999'950'885, .paymentInterval = 60, .paymentTotal = 31'625, .expected = tesSUCCESS},
        {.principal = 999'950'886, .paymentInterval = 60, .paymentTotal = 31'621, .expected = tesSUCCESS},
        {.principal = 999'950'886, .paymentInterval = 60, .paymentTotal = 31'622, .expected = tesSUCCESS},
        {.principal = 999'950'886, .paymentInterval = 60, .paymentTotal = 31'623, .expected = tesSUCCESS},
        {.principal = 999'950'886, .paymentInterval = 60, .paymentTotal = 31'624, .expected = tesSUCCESS},
        {.principal = 999'950'886, .paymentInterval = 60, .paymentTotal = 31'625, .expected = tesSUCCESS},
        {.principal = 999'950'887, .paymentInterval = 60, .paymentTotal = 31'621, .expected = tesSUCCESS},
        {.principal = 999'950'887, .paymentInterval = 60, .paymentTotal = 31'622, .expected = tesSUCCESS},
        {.principal = 999'950'887, .paymentInterval = 60, .paymentTotal = 31'623, .expected = tesSUCCESS},
        {.principal = 999'950'887, .paymentInterval = 60, .paymentTotal = 31'624, .expected = tesSUCCESS},
        {.principal = 999'950'887, .paymentInterval = 60, .paymentTotal = 31'625, .expected = tesSUCCESS},
        // count 1'000'000, principal 1'000'000
        {.principal = 999'998, .paymentInterval = 60, .paymentTotal = 999'998, .expected = tesSUCCESS},
        {.principal = 999'998, .paymentInterval = 60, .paymentTotal = 999'999, .expected = tecPRECISION_LOSS},
        {.principal = 999'998, .paymentInterval = 60, .paymentTotal = 1'000'000, .expected = tecPRECISION_LOSS},
        {.principal = 999'998, .paymentInterval = 60, .paymentTotal = 1'000'001, .expected = tecPRECISION_LOSS},
        {.principal = 999'998, .paymentInterval = 60, .paymentTotal = 1'000'002, .expected = tecPRECISION_LOSS},
        {.principal = 999'999, .paymentInterval = 60, .paymentTotal = 999'998, .expected = tecPRECISION_LOSS},
        {.principal = 999'999, .paymentInterval = 60, .paymentTotal = 999'999, .expected = tesSUCCESS},
        {.principal = 999'999, .paymentInterval = 60, .paymentTotal = 1'000'000, .expected = tecPRECISION_LOSS},
        {.principal = 999'999, .paymentInterval = 60, .paymentTotal = 1'000'001, .expected = tecPRECISION_LOSS},
        {.principal = 999'999, .paymentInterval = 60, .paymentTotal = 1'000'002, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000, .paymentInterval = 60, .paymentTotal = 999'998, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000, .paymentInterval = 60, .paymentTotal = 999'999, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000, .paymentInterval = 60, .paymentTotal = 1'000'000, .expected = tesSUCCESS},
        {.principal = 1'000'000, .paymentInterval = 60, .paymentTotal = 1'000'001, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000, .paymentInterval = 60, .paymentTotal = 1'000'002, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'001, .paymentInterval = 60, .paymentTotal = 999'998, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'001, .paymentInterval = 60, .paymentTotal = 999'999, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'001, .paymentInterval = 60, .paymentTotal = 1'000'000, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'001, .paymentInterval = 60, .paymentTotal = 1'000'001, .expected = tesSUCCESS},
        {.principal = 1'000'001, .paymentInterval = 60, .paymentTotal = 1'000'002, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'002, .paymentInterval = 60, .paymentTotal = 999'998, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'002, .paymentInterval = 60, .paymentTotal = 999'999, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'002, .paymentInterval = 60, .paymentTotal = 1'000'000, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'002, .paymentInterval = 60, .paymentTotal = 1'000'001, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'002, .paymentInterval = 60, .paymentTotal = 1'000'002, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kRedemptionBuffer[] = {
        // interval 60 x 1: redemption 120 after the start
        {.subscription = -1'000, .redemption = 1'118, .principal = 500, .paymentInterval = 60, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'118, .principal = 1'000, .paymentInterval = 60, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'118, .principal = 1'500, .paymentInterval = 60, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'119, .principal = 500, .paymentInterval = 60, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'119, .principal = 1'000, .paymentInterval = 60, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'119, .principal = 1'500, .paymentInterval = 60, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'120, .principal = 500, .paymentInterval = 60, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'120, .principal = 1'000, .paymentInterval = 60, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'120, .principal = 1'500, .paymentInterval = 60, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'121, .principal = 500, .paymentInterval = 60, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'121, .principal = 1'000, .paymentInterval = 60, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'121, .principal = 1'500, .paymentInterval = 60, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'122, .principal = 500, .paymentInterval = 60, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'122, .principal = 1'000, .paymentInterval = 60, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'122, .principal = 1'500, .paymentInterval = 60, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        // interval 1'000'000 x 1: redemption 1'000'060 after the start
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 500, .paymentInterval = 1'000'000, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 1'000, .paymentInterval = 1'000'000, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 1'500, .paymentInterval = 1'000'000, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 500, .paymentInterval = 1'000'000, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 1'000, .paymentInterval = 1'000'000, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 1'500, .paymentInterval = 1'000'000, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 500, .paymentInterval = 1'000'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 1'000, .paymentInterval = 1'000'000, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 1'500, .paymentInterval = 1'000'000, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 500, .paymentInterval = 1'000'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 1'000, .paymentInterval = 1'000'000, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 1'500, .paymentInterval = 1'000'000, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 500, .paymentInterval = 1'000'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 1'000, .paymentInterval = 1'000'000, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 1'500, .paymentInterval = 1'000'000, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        // interval 100 x 10'000: redemption 1'000'060 after the start
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 4'999'000, .paymentInterval = 100, .paymentTotal = 9'998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 4'999'500, .paymentInterval = 100, .paymentTotal = 9'999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 5'000'000, .paymentInterval = 100, .paymentTotal = 10'000, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 5'000'500, .paymentInterval = 100, .paymentTotal = 10'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 5'001'000, .paymentInterval = 100, .paymentTotal = 10'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 4'999'000, .paymentInterval = 100, .paymentTotal = 9'998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 4'999'500, .paymentInterval = 100, .paymentTotal = 9'999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 5'000'000, .paymentInterval = 100, .paymentTotal = 10'000, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 5'000'500, .paymentInterval = 100, .paymentTotal = 10'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 5'001'000, .paymentInterval = 100, .paymentTotal = 10'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 4'999'000, .paymentInterval = 100, .paymentTotal = 9'998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 4'999'500, .paymentInterval = 100, .paymentTotal = 9'999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 5'000'000, .paymentInterval = 100, .paymentTotal = 10'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 5'000'500, .paymentInterval = 100, .paymentTotal = 10'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 5'001'000, .paymentInterval = 100, .paymentTotal = 10'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 4'999'000, .paymentInterval = 100, .paymentTotal = 9'998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 4'999'500, .paymentInterval = 100, .paymentTotal = 9'999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 5'000'000, .paymentInterval = 100, .paymentTotal = 10'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 5'000'500, .paymentInterval = 100, .paymentTotal = 10'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 5'001'000, .paymentInterval = 100, .paymentTotal = 10'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 4'999'000, .paymentInterval = 100, .paymentTotal = 9'998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 4'999'500, .paymentInterval = 100, .paymentTotal = 9'999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 5'000'000, .paymentInterval = 100, .paymentTotal = 10'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 5'000'500, .paymentInterval = 100, .paymentTotal = 10'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 5'001'000, .paymentInterval = 100, .paymentTotal = 10'002, .start = 1'000, .expected = tecNO_PERMISSION},
        // interval 1'000 x 1'000: redemption 1'000'060 after the start
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 499'000, .paymentInterval = 1'000, .paymentTotal = 998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 499'500, .paymentInterval = 1'000, .paymentTotal = 999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 500'000, .paymentInterval = 1'000, .paymentTotal = 1'000, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 500'500, .paymentInterval = 1'000, .paymentTotal = 1'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'058, .principal = 501'000, .paymentInterval = 1'000, .paymentTotal = 1'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 499'000, .paymentInterval = 1'000, .paymentTotal = 998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 499'500, .paymentInterval = 1'000, .paymentTotal = 999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 500'000, .paymentInterval = 1'000, .paymentTotal = 1'000, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 500'500, .paymentInterval = 1'000, .paymentTotal = 1'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'059, .principal = 501'000, .paymentInterval = 1'000, .paymentTotal = 1'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 499'000, .paymentInterval = 1'000, .paymentTotal = 998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 499'500, .paymentInterval = 1'000, .paymentTotal = 999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 500'000, .paymentInterval = 1'000, .paymentTotal = 1'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 500'500, .paymentInterval = 1'000, .paymentTotal = 1'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'060, .principal = 501'000, .paymentInterval = 1'000, .paymentTotal = 1'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 499'000, .paymentInterval = 1'000, .paymentTotal = 998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 499'500, .paymentInterval = 1'000, .paymentTotal = 999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 500'000, .paymentInterval = 1'000, .paymentTotal = 1'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 500'500, .paymentInterval = 1'000, .paymentTotal = 1'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'061, .principal = 501'000, .paymentInterval = 1'000, .paymentTotal = 1'002, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 499'000, .paymentInterval = 1'000, .paymentTotal = 998, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 499'500, .paymentInterval = 1'000, .paymentTotal = 999, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 500'000, .paymentInterval = 1'000, .paymentTotal = 1'000, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 500'500, .paymentInterval = 1'000, .paymentTotal = 1'001, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 1'001'062, .principal = 501'000, .paymentInterval = 1'000, .paymentTotal = 1'002, .start = 1'000, .expected = tecNO_PERMISSION},
        // interval 945'999'960 x 1: redemption 946'000'020 after the start
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 500, .paymentInterval = 945'999'960, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 1'000, .paymentInterval = 945'999'960, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 1'500, .paymentInterval = 945'999'960, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 500, .paymentInterval = 945'999'960, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 1'000, .paymentInterval = 945'999'960, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 1'500, .paymentInterval = 945'999'960, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 500, .paymentInterval = 945'999'960, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 1'000, .paymentInterval = 945'999'960, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 1'500, .paymentInterval = 945'999'960, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 500, .paymentInterval = 945'999'960, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 1'000, .paymentInterval = 945'999'960, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 1'500, .paymentInterval = 945'999'960, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 500, .paymentInterval = 945'999'960, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 1'000, .paymentInterval = 945'999'960, .paymentTotal = 2, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 1'500, .paymentInterval = 945'999'960, .paymentTotal = 3, .start = 1'000, .expected = tecNO_PERMISSION},
        // interval 60 x 15'766'666: redemption 946'000'020 after the start
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 7'883'332'000, .paymentInterval = 60, .paymentTotal = 15'766'664, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 7'883'332'500, .paymentInterval = 60, .paymentTotal = 15'766'665, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 7'883'333'000, .paymentInterval = 60, .paymentTotal = 15'766'666, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 7'883'333'500, .paymentInterval = 60, .paymentTotal = 15'766'667, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'018, .principal = 7'883'334'000, .paymentInterval = 60, .paymentTotal = 15'766'668, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 7'883'332'000, .paymentInterval = 60, .paymentTotal = 15'766'664, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 7'883'332'500, .paymentInterval = 60, .paymentTotal = 15'766'665, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 7'883'333'000, .paymentInterval = 60, .paymentTotal = 15'766'666, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 7'883'333'500, .paymentInterval = 60, .paymentTotal = 15'766'667, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'019, .principal = 7'883'334'000, .paymentInterval = 60, .paymentTotal = 15'766'668, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 7'883'332'000, .paymentInterval = 60, .paymentTotal = 15'766'664, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 7'883'332'500, .paymentInterval = 60, .paymentTotal = 15'766'665, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 7'883'333'000, .paymentInterval = 60, .paymentTotal = 15'766'666, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 7'883'333'500, .paymentInterval = 60, .paymentTotal = 15'766'667, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'020, .principal = 7'883'334'000, .paymentInterval = 60, .paymentTotal = 15'766'668, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 7'883'332'000, .paymentInterval = 60, .paymentTotal = 15'766'664, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 7'883'332'500, .paymentInterval = 60, .paymentTotal = 15'766'665, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 7'883'333'000, .paymentInterval = 60, .paymentTotal = 15'766'666, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 7'883'333'500, .paymentInterval = 60, .paymentTotal = 15'766'667, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'021, .principal = 7'883'334'000, .paymentInterval = 60, .paymentTotal = 15'766'668, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 7'883'332'000, .paymentInterval = 60, .paymentTotal = 15'766'664, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 7'883'332'500, .paymentInterval = 60, .paymentTotal = 15'766'665, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 7'883'333'000, .paymentInterval = 60, .paymentTotal = 15'766'666, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 7'883'333'500, .paymentInterval = 60, .paymentTotal = 15'766'667, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 946'001'022, .principal = 7'883'334'000, .paymentInterval = 60, .paymentTotal = 15'766'668, .start = 1'000, .expected = tecNO_PERMISSION},
        // interval 30'000 x 31'533: redemption 945'990'060 after the start
        {.subscription = -1'000, .redemption = 945'991'058, .principal = 15'765'500, .paymentInterval = 30'000, .paymentTotal = 31'531, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'058, .principal = 15'766'000, .paymentInterval = 30'000, .paymentTotal = 31'532, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'058, .principal = 15'766'500, .paymentInterval = 30'000, .paymentTotal = 31'533, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'058, .principal = 15'767'000, .paymentInterval = 30'000, .paymentTotal = 31'534, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'058, .principal = 15'767'500, .paymentInterval = 30'000, .paymentTotal = 31'535, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'059, .principal = 15'765'500, .paymentInterval = 30'000, .paymentTotal = 31'531, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'059, .principal = 15'766'000, .paymentInterval = 30'000, .paymentTotal = 31'532, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'059, .principal = 15'766'500, .paymentInterval = 30'000, .paymentTotal = 31'533, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'059, .principal = 15'767'000, .paymentInterval = 30'000, .paymentTotal = 31'534, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'059, .principal = 15'767'500, .paymentInterval = 30'000, .paymentTotal = 31'535, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'060, .principal = 15'765'500, .paymentInterval = 30'000, .paymentTotal = 31'531, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'060, .principal = 15'766'000, .paymentInterval = 30'000, .paymentTotal = 31'532, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'060, .principal = 15'766'500, .paymentInterval = 30'000, .paymentTotal = 31'533, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'060, .principal = 15'767'000, .paymentInterval = 30'000, .paymentTotal = 31'534, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'060, .principal = 15'767'500, .paymentInterval = 30'000, .paymentTotal = 31'535, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'061, .principal = 15'765'500, .paymentInterval = 30'000, .paymentTotal = 31'531, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'061, .principal = 15'766'000, .paymentInterval = 30'000, .paymentTotal = 31'532, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'061, .principal = 15'766'500, .paymentInterval = 30'000, .paymentTotal = 31'533, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'061, .principal = 15'767'000, .paymentInterval = 30'000, .paymentTotal = 31'534, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'061, .principal = 15'767'500, .paymentInterval = 30'000, .paymentTotal = 31'535, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'062, .principal = 15'765'500, .paymentInterval = 30'000, .paymentTotal = 31'531, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'062, .principal = 15'766'000, .paymentInterval = 30'000, .paymentTotal = 31'532, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'062, .principal = 15'766'500, .paymentInterval = 30'000, .paymentTotal = 31'533, .start = 1'000, .expected = tesSUCCESS},
        {.subscription = -1'000, .redemption = 945'991'062, .principal = 15'767'000, .paymentInterval = 30'000, .paymentTotal = 31'534, .start = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -1'000, .redemption = 945'991'062, .principal = 15'767'500, .paymentInterval = 30'000, .paymentTotal = 31'535, .start = 1'000, .expected = tecNO_PERMISSION},
    };
    static constexpr LoanSetCase kOpenZone[] = {
        // yield 8'999'989'999'999'999, principal 10
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        // yield 8'999'989'900'000'000, principal 1'000'000'000
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr LoanSetCase kPrincipalGrid[] = {
        // one step of 1e0 units
        {.principal = 999'999'999'999'998, .principalExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 999'999'999'999'999, .principalExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000'000'000'000, .principalExponent = -15, .expected = tesSUCCESS},
        {.principal = 1'000'000'000'000'001, .principalExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000'000'000'002, .principalExponent = -15, .expected = tecPRECISION_LOSS},
        // one step of 1e9 units
        {.principal = 999'999'999'999'998, .principalExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 999'999'999'999'999, .principalExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000'000'000'000, .principalExponent = -6, .expected = tesSUCCESS},
        {.principal = 1'000'000'000'000'001, .principalExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000'000'000'002, .principalExponent = -6, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kOriginationFeeGrid[] = {
        // one step of 1e0 units
        {.principal = 2'000'000'000, .originationFee = 999'999'999'999'998, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .originationFee = 999'999'999'999'999, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .originationFee = 1'000'000'000'000'000, .feeExponent = -15, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .originationFee = 1'000'000'000'000'001, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .originationFee = 1'000'000'000'000'002, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        // one step of 1e9 units
        {.principal = 2'000'000'000, .originationFee = 999'999'999'999'998, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .originationFee = 999'999'999'999'999, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .originationFee = 1'000'000'000'000'000, .feeExponent = -6, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .originationFee = 1'000'000'000'000'001, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .originationFee = 1'000'000'000'000'002, .feeExponent = -6, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kServiceFeeGrid[] = {
        // one step of 1e0 units
        {.principal = 2'000'000'000, .serviceFee = 999'999'999'999'998, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .serviceFee = 999'999'999'999'999, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .serviceFee = 1'000'000'000'000'000, .feeExponent = -15, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .serviceFee = 1'000'000'000'000'001, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .serviceFee = 1'000'000'000'000'002, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        // one step of 1e9 units
        {.principal = 2'000'000'000, .serviceFee = 999'999'999'999'998, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .serviceFee = 999'999'999'999'999, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .serviceFee = 1'000'000'000'000'000, .feeExponent = -6, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .serviceFee = 1'000'000'000'000'001, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .serviceFee = 1'000'000'000'000'002, .feeExponent = -6, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kLateFeeGrid[] = {
        // one step of 1e0 units
        {.principal = 2'000'000'000, .latePaymentFee = 999'999'999'999'998, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .latePaymentFee = 999'999'999'999'999, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .latePaymentFee = 1'000'000'000'000'000, .feeExponent = -15, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .latePaymentFee = 1'000'000'000'000'001, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .latePaymentFee = 1'000'000'000'000'002, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        // one step of 1e9 units
        {.principal = 2'000'000'000, .latePaymentFee = 999'999'999'999'998, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .latePaymentFee = 999'999'999'999'999, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .latePaymentFee = 1'000'000'000'000'000, .feeExponent = -6, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .latePaymentFee = 1'000'000'000'000'001, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .latePaymentFee = 1'000'000'000'000'002, .feeExponent = -6, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kCloseFeeGrid[] = {
        // one step of 1e0 units
        {.principal = 2'000'000'000, .closePaymentFee = 999'999'999'999'998, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .closePaymentFee = 999'999'999'999'999, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .closePaymentFee = 1'000'000'000'000'000, .feeExponent = -15, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .closePaymentFee = 1'000'000'000'000'001, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .closePaymentFee = 1'000'000'000'000'002, .feeExponent = -15, .expected = tecPRECISION_LOSS},
        // one step of 1e9 units
        {.principal = 2'000'000'000, .closePaymentFee = 999'999'999'999'998, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .closePaymentFee = 999'999'999'999'999, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .closePaymentFee = 1'000'000'000'000'000, .feeExponent = -6, .expected = tesSUCCESS},
        {.principal = 2'000'000'000, .closePaymentFee = 1'000'000'000'000'001, .feeExponent = -6, .expected = tecPRECISION_LOSS},
        {.principal = 2'000'000'000, .closePaymentFee = 1'000'000'000'000'002, .feeExponent = -6, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kSubscriptionDate[] = {
        // subscription date
        {.subscription = -2, .redemption = 900'000'000, .principal = 1'000, .expected = tesSUCCESS},
        {.subscription = -1, .redemption = 900'000'000, .principal = 1'000, .expected = tesSUCCESS},
        {.subscription = 0, .redemption = 900'000'000, .principal = 1'000, .expected = tecTOO_SOON},
        {.subscription = 1, .redemption = 900'000'000, .principal = 1'000, .expected = tecTOO_SOON},
        {.subscription = 2, .redemption = 900'000'000, .principal = 1'000, .expected = tecTOO_SOON},
    };
    static constexpr LoanSetCase kRedemptionDate[] = {
        // redemption date
        {.subscription = -1'000'002, .redemption = -2, .principal = 1'000, .expected = tecEXPIRED},
        {.subscription = -1'000'001, .redemption = -1, .principal = 1'000, .expected = tecEXPIRED},
        {.subscription = -1'000'000, .redemption = 0, .principal = 1'000, .expected = tecEXPIRED},
        {.subscription = -999'999, .redemption = 1, .principal = 1'000, .expected = tecNO_PERMISSION},
        {.subscription = -999'998, .redemption = 2, .principal = 1'000, .expected = tecNO_PERMISSION},
    };
    static constexpr LoanSetCase kStartDate[] = {
        // start date
        {.principal = 1'000, .start = -2, .expected = tecEXPIRED},
        {.principal = 1'000, .start = -1, .expected = tecEXPIRED},
        {.principal = 1'000, .start = 0, .expected = tecEXPIRED},
        {.principal = 1'000, .start = 1, .expected = tesSUCCESS},
        {.principal = 1'000, .start = 2, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kOriginationFee[] = {
        // fee 1 = principal 1
        {.principal = 1, .originationFee = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1, .expected = tesSUCCESS},
        {.principal = 1, .originationFee = 1, .expected = tesSUCCESS},
        {.principal = 1, .originationFee = 2, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1, .originationFee = 3, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 2, .originationFee = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 2, .expected = tesSUCCESS},
        {.principal = 2, .originationFee = 1, .expected = tesSUCCESS},
        {.principal = 2, .originationFee = 2, .expected = tesSUCCESS},
        {.principal = 2, .originationFee = 3, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 3, .originationFee = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 3, .expected = tesSUCCESS},
        {.principal = 3, .originationFee = 1, .expected = tesSUCCESS},
        {.principal = 3, .originationFee = 2, .expected = tesSUCCESS},
        {.principal = 3, .originationFee = 3, .expected = tesSUCCESS},
        // fee 1'000'000'000 = principal 1'000'000'000
        {.principal = 999'999'998, .originationFee = 999'999'998, .expected = tesSUCCESS},
        {.principal = 999'999'998, .originationFee = 999'999'999, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 999'999'998, .originationFee = 1'000'000'000, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 999'999'998, .originationFee = 1'000'000'001, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 999'999'998, .originationFee = 1'000'000'002, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 999'999'999, .originationFee = 999'999'998, .expected = tesSUCCESS},
        {.principal = 999'999'999, .originationFee = 999'999'999, .expected = tesSUCCESS},
        {.principal = 999'999'999, .originationFee = 1'000'000'000, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 999'999'999, .originationFee = 1'000'000'001, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 999'999'999, .originationFee = 1'000'000'002, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .originationFee = 999'999'998, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .originationFee = 999'999'999, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .originationFee = 1'000'000'000, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .originationFee = 1'000'000'001, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .originationFee = 1'000'000'002, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'001, .originationFee = 999'999'998, .expected = tesSUCCESS},
        {.principal = 1'000'000'001, .originationFee = 999'999'999, .expected = tesSUCCESS},
        {.principal = 1'000'000'001, .originationFee = 1'000'000'000, .expected = tesSUCCESS},
        {.principal = 1'000'000'001, .originationFee = 1'000'000'001, .expected = tesSUCCESS},
        {.principal = 1'000'000'001, .originationFee = 1'000'000'002, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'002, .originationFee = 999'999'998, .expected = tesSUCCESS},
        {.principal = 1'000'000'002, .originationFee = 999'999'999, .expected = tesSUCCESS},
        {.principal = 1'000'000'002, .originationFee = 1'000'000'000, .expected = tesSUCCESS},
        {.principal = 1'000'000'002, .originationFee = 1'000'000'001, .expected = tesSUCCESS},
        {.principal = 1'000'000'002, .originationFee = 1'000'000'002, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kPrincipalAndPayments[] = {
        // principal 0, one-step
        // Lean create tecPRECISION_LOSS (first payment pays no principal), not notLawful.
        // {.principal = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        // {.principal = 0, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1, .expected = tesSUCCESS},
        // principal 0, two-step
        // Lean create tecPRECISION_LOSS (first payment pays no principal), not notLawful.
        // {.principal = -1, .start = 1'000, .expected = temINVALID, .leanError = LeanError::notLawful},
        // {.principal = 0, .start = 1'000, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1, .start = 1'000, .expected = tesSUCCESS},
        // payment total 0, one-step
        // Lean create error wrap, not notLawful.
        // {.principal = 1'000, .paymentTotal = 0, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000, .paymentTotal = 1, .expected = tesSUCCESS},
        // payment total 0, two-step
        // Lean create error wrap, not notLawful.
        // {.principal = 1'000, .paymentTotal = 0, .start = 1'000, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000, .paymentTotal = 1, .start = 1'000, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kPrincipalCap[] = {
        // 2^63 - 1 at exponent 3
        {.principal = 9'223'372'036'854'773, .principalExponent = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.principal = 9'223'372'036'854'774, .principalExponent = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.principal = 9'223'372'036'854'775, .principalExponent = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.principal = 9'223'372'036'854'776, .principalExponent = 3, .expected = tecPRECISION_LOSS},
        {.principal = 9'223'372'036'854'777, .principalExponent = 3, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kServiceFeeCap[] = {
        // 2^63 - 1 at exponent 3
        {.principal = 1'000'000'000, .serviceFee = 9'223'372'036'854'773, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .serviceFee = 9'223'372'036'854'774, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .serviceFee = 9'223'372'036'854'775, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .serviceFee = 9'223'372'036'854'776, .feeExponent = 3, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000'000, .serviceFee = 9'223'372'036'854'777, .feeExponent = 3, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kLateFeeCap[] = {
        // 2^63 - 1 at exponent 3
        {.principal = 1'000'000'000, .latePaymentFee = 9'223'372'036'854'773, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .latePaymentFee = 9'223'372'036'854'774, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .latePaymentFee = 9'223'372'036'854'775, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .latePaymentFee = 9'223'372'036'854'776, .feeExponent = 3, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000'000, .latePaymentFee = 9'223'372'036'854'777, .feeExponent = 3, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kCloseFeeCap[] = {
        // 2^63 - 1 at exponent 3
        {.principal = 1'000'000'000, .closePaymentFee = 9'223'372'036'854'773, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .closePaymentFee = 9'223'372'036'854'774, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .closePaymentFee = 9'223'372'036'854'775, .feeExponent = 3, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .closePaymentFee = 9'223'372'036'854'776, .feeExponent = 3, .expected = tecPRECISION_LOSS},
        {.principal = 1'000'000'000, .closePaymentFee = 9'223'372'036'854'777, .feeExponent = 3, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanSetCase kServiceFeeMinimum[] = {
        // zero
        {.principal = 1'000'000'000, .serviceFee = -2, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .serviceFee = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .serviceFee = 1, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .serviceFee = 2, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kLateFeeMinimum[] = {
        // zero
        {.principal = 1'000'000'000, .latePaymentFee = -2, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .latePaymentFee = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .latePaymentFee = 1, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .latePaymentFee = 2, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kCloseFeeMinimum[] = {
        // zero
        {.principal = 1'000'000'000, .closePaymentFee = -2, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .closePaymentFee = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.principal = 1'000'000'000, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .closePaymentFee = 1, .expected = tesSUCCESS},
        {.principal = 1'000'000'000, .closePaymentFee = 2, .expected = tesSUCCESS},
    };
    static constexpr LoanSetCase kTimeLimit[] = {
        // start 4'294'967'175, interval 60 x 1, grace 60
        {.principal = 1'000'000'000, .paymentInterval = 60, .gracePeriod = 60, .startAt = 4'294'967'175, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentInterval = 60, .paymentTotal = 2, .gracePeriod = 60, .startAt = 4'294'967'175, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 60, .paymentTotal = 3, .gracePeriod = 60, .startAt = 4'294'967'175, .expected = tecKILLED},
        // start 4'294'366'695, interval 600 x 1'000, grace 600
        {.principal = 1'000'000'000, .paymentTotal = 998, .gracePeriod = 598, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 999, .gracePeriod = 598, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 1'000, .gracePeriod = 598, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 1'001, .gracePeriod = 598, .startAt = 4'294'366'695, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentTotal = 1'002, .gracePeriod = 598, .startAt = 4'294'366'695, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentTotal = 998, .gracePeriod = 599, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 999, .gracePeriod = 599, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 1'000, .gracePeriod = 599, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 1'001, .gracePeriod = 599, .startAt = 4'294'366'695, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentTotal = 1'002, .gracePeriod = 599, .startAt = 4'294'366'695, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentTotal = 998, .gracePeriod = 600, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 999, .gracePeriod = 600, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 1'000, .gracePeriod = 600, .startAt = 4'294'366'695, .expected = tecNO_PERMISSION},
        {.principal = 1'000'000'000, .paymentTotal = 1'001, .gracePeriod = 600, .startAt = 4'294'366'695, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentTotal = 1'002, .gracePeriod = 600, .startAt = 4'294'366'695, .expected = tecKILLED},
        // start 0, interval 4'294'967'235 x 1, grace 60
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .gracePeriod = 60, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .paymentTotal = 2, .gracePeriod = 60, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .paymentTotal = 3, .gracePeriod = 60, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .gracePeriod = 61, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .paymentTotal = 2, .gracePeriod = 61, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .paymentTotal = 3, .gracePeriod = 61, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .gracePeriod = 62, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .paymentTotal = 2, .gracePeriod = 62, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 4'294'967'235, .paymentTotal = 3, .gracePeriod = 62, .startAt = 0, .expected = tecKILLED},
        // start 0, interval 64 x 67'108'863, grace 63
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'861, .gracePeriod = 61, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'862, .gracePeriod = 61, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'863, .gracePeriod = 61, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'864, .gracePeriod = 61, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'865, .gracePeriod = 61, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'861, .gracePeriod = 62, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'862, .gracePeriod = 62, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'863, .gracePeriod = 62, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'864, .gracePeriod = 62, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'865, .gracePeriod = 62, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'861, .gracePeriod = 63, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'862, .gracePeriod = 63, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'863, .gracePeriod = 63, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'864, .gracePeriod = 63, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'865, .gracePeriod = 63, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'861, .gracePeriod = 64, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'862, .gracePeriod = 64, .startAt = 0, .expected = tecEXPIRED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'863, .gracePeriod = 64, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'864, .gracePeriod = 64, .startAt = 0, .expected = tecKILLED},
        {.principal = 1'000'000'000, .paymentInterval = 64, .paymentTotal = 67'108'865, .gracePeriod = 64, .startAt = 0, .expected = tecKILLED},
    };
    static constexpr LoanAcceptCase kAcceptStartDate[] = {
        // start date
        {.principal = 1'000, .start = -2, .expected = tecEXPIRED},
        {.principal = 1'000, .start = -1, .expected = tecEXPIRED},
        {.principal = 1'000, .start = 0, .expected = tecEXPIRED},
        {.principal = 1'000, .start = 1, .expected = tesSUCCESS},
        {.principal = 1'000, .start = 2, .expected = tesSUCCESS},
    };
    static constexpr LoanAcceptCase kAcceptSubscriptionDate[] = {
        // subscription date
        {.principal = 1'000, .subscription = -2, .redemption = 900'000'000, .expected = tesSUCCESS},
        {.principal = 1'000, .subscription = -1, .redemption = 900'000'000, .expected = tesSUCCESS},
        {.principal = 1'000, .subscription = 0, .redemption = 900'000'000, .expected = tecTOO_SOON},
        {.principal = 1'000, .subscription = 1, .redemption = 900'000'000, .expected = tecTOO_SOON},
        {.principal = 1'000, .subscription = 2, .redemption = 900'000'000, .expected = tecTOO_SOON},
    };
    static constexpr LoanAcceptCase kAcceptRedemptionDate[] = {
        // redemption date
        {.principal = 1'000, .subscription = -1'000'002, .redemption = -2, .expected = tecEXPIRED},
        {.principal = 1'000, .subscription = -1'000'001, .redemption = -1, .expected = tecEXPIRED},
        {.principal = 1'000, .subscription = -1'000'000, .redemption = 0, .expected = tecEXPIRED},
        {.principal = 1'000, .subscription = -999'999, .redemption = 1, .expected = tesSUCCESS},
        {.principal = 1'000, .subscription = -999'998, .redemption = 2, .expected = tesSUCCESS},
    };
    static constexpr LoanAcceptCase kAcceptOpenZone[] = {
        // yield 8'999'989'999'999'999, principal 10
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'997}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'998}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'999'999'999}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'000}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 8, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 9, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 10, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 11, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'990'000'000'001}, .principal = 12, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        // yield 8'999'989'900'000'000, principal 1'000'000'000
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'998}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'899'999'999}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tesSUCCESS},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'000}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'001}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 999'999'998, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 999'999'999, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 1'000'000'000, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 1'000'000'001, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.yield = 8'999'989'900'000'002}, .principal = 1'000'000'002, .interestRate = 100'000, .paymentInterval = 3'153'600, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr LoanDeleteCase kDeleteRemaining[] = {
        // active: 3, 2, 1, 0 payments remaining
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tecHAS_OBLIGATIONS},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 1, .expected = tecHAS_OBLIGATIONS},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 2, .expected = tecHAS_OBLIGATIONS},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 3, .expected = tesSUCCESS},
        // proposal: all payments remaining
        {.principal = 1'200'000'000, .paymentTotal = 3, .expected = tesSUCCESS, .pending = true},
        {.principal = 1'200'000'000, .interestRate = 10'000, .paymentTotal = 3, .expected = tesSUCCESS, .pending = true},
        // defaulted: no payments remaining
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tesSUCCESS, .defaulted = true},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 2, .expected = tesSUCCESS, .defaulted = true},
    };
    static constexpr LoanDeleteCase kDeleteBesideLoan[] = {
        // another loan of 1'000'000'000
        {.debt = 1'000'000'000, .principal = 1'200'000'000, .paymentTotal = 3, .expected = tesSUCCESS, .pending = true},
        {.debt = 1'000'000'000, .principal = 1'200'000'000, .interestRate = 10'000, .paymentTotal = 3, .expected = tesSUCCESS, .pending = true},
        {.debt = 1'000'000'000, .principal = 1'200'000'000, .paymentTotal = 3, .paid = 3, .expected = tesSUCCESS},
        {.debt = 1'000'000'000, .principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tesSUCCESS, .defaulted = true},
    };
    static constexpr LoanDeleteCase kDeleteParty[] = {
        // broker owner
        {.principal = 1'200'000'000, .paymentTotal = 3, .expected = tesSUCCESS, .pending = true, .by = DeleteParty::Owner},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 3, .expected = tesSUCCESS, .by = DeleteParty::Owner},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tecHAS_OBLIGATIONS, .by = DeleteParty::Owner},
        // neither owner nor borrower
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tecHAS_OBLIGATIONS, .by = DeleteParty::Other},
        // Lean tesSUCCESS: canDelete takes no submitting account.
        // {.principal = 1'200'000'000, .paymentTotal = 3, .expected = tecNO_PERMISSION, .pending = true, .by = DeleteParty::Other},
        // {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 3, .expected = tecNO_PERMISSION, .by = DeleteParty::Other},
    };
    static constexpr LoanDeleteCase kDeleteImpaired[] = {
        // impaired: payments remain
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tecHAS_OBLIGATIONS, .impaired = true},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 2, .expected = tecHAS_OBLIGATIONS, .impaired = true},
        {.principal = 1'200'000'000, .interestRate = 10'000, .paymentTotal = 3, .paid = 0, .expected = tecHAS_OBLIGATIONS, .impaired = true},
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tecHAS_OBLIGATIONS, .by = DeleteParty::Owner, .impaired = true},
        // impaired, then defaulted
        {.principal = 1'200'000'000, .paymentTotal = 3, .paid = 0, .expected = tesSUCCESS, .defaulted = true, .impaired = true},
    };
    // clang-format on

    void
    runLoanSetBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanSetCase const> cases) {
            testcase("LoanSet " + name);
            for (TestLedger const& ledger : ledgers)
            {
                for (std::size_t i = 0; LoanSetCase const& c : cases)
                {
                    jtx::Env& env = *ledger.env;
                    std::uint32_t const parentClose = parentCloseTime(env);
                    LoanParams p{
                        .principal = units(ledger.f, c.principal, c.principalExponent),
                        .interestRate = c.interestRate,
                        .originationFee = units(ledger.f, c.originationFee, c.feeExponent),
                        .serviceFee = units(ledger.f, c.serviceFee, c.feeExponent),
                        .latePaymentFee = units(ledger.f, c.latePaymentFee, c.feeExponent),
                        .closePaymentFee = units(ledger.f, c.closePaymentFee, c.feeExponent),
                        .paymentInterval = c.paymentInterval,
                        .paymentTotal = c.paymentTotal,
                        .gracePeriod = c.gracePeriod,
                    };
                    if (c.start)
                        p.startDate = static_cast<std::uint32_t>(parentClose + *c.start);
                    if (c.startAt)
                        p.startDate = c.startAt;
                    LendingStage stage = c.stage;
                    if (c.subscription)
                    {
                        stage.subscriptionDate =
                            static_cast<std::uint32_t>(parentClose + *c.subscription);
                        stage.redemptionDate =
                            static_cast<std::uint32_t>(parentClose + c.redemption.value());
                    }
                    std::string const at =
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)) +
                        stageText(stage) + loanText(p) + ": ";
                    OpenView view{*env.current()};
                    if (!tryStage(*this, at, [&] {
                            if (c.subscription)
                            {
                                stageLending(env, view, ledger.f, stage);
                            }
                            else
                            {
                                stageInvestment(env, view, ledger.f, stage);
                            }
                        }))
                        continue;
                    checkLoanSet(env, ledger.f, view, p, c.expected, c.leanError, at);
                }
            }
        };

        run("debt maximum", s.all, kDebtMaximum);
        run("debt maximum with interest", s.all, kDebtMaximumWithInterest);
        run("assets available", s.all, kAssetsAvailable);
        run("cover at origination", s.all, kOriginationCover);
        run("payment count", s.all, kPaymentCount);
        run("redemption buffer", s.iou, kRedemptionBuffer);
        run("open zone", s.all, kOpenZone);
        run("principal grid", s.all, kPrincipalGrid);
        run("origination fee grid", s.all, kOriginationFeeGrid);
        run("service fee grid", s.all, kServiceFeeGrid);
        run("late fee grid", s.all, kLateFeeGrid);
        run("close fee grid", s.all, kCloseFeeGrid);
        run("subscription date", s.iou, kSubscriptionDate);
        run("redemption date", s.iou, kRedemptionDate);
        run("start date", s.iou, kStartDate);
        run("origination fee", s.all, kOriginationFee);
        run("principal and payments", s.all, kPrincipalAndPayments);
        run("principal cap", s.mpt, kPrincipalCap);
        run("service fee cap", s.mpt, kServiceFeeCap);
        run("late fee cap", s.mpt, kLateFeeCap);
        run("close fee cap", s.mpt, kCloseFeeCap);
        run("service fee minimum", s.all, kServiceFeeMinimum);
        run("late fee minimum", s.all, kLateFeeMinimum);
        run("close fee minimum", s.all, kCloseFeeMinimum);
        run("protocol time limit", s.iou, kTimeLimit);
    }

    void
    testLoanSetBoundaries(LendingSetup const& s)
    {
        runLoanSetBoundaries(s);
    }

    void
    runLoanAcceptBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanAcceptCase const> cases) {
            testcase("LoanAccept " + name);
            for (TestLedger const& ledger : ledgers)
            {
                for (std::size_t i = 0; LoanAcceptCase const& c : cases)
                {
                    jtx::Env& env = *ledger.env;
                    std::uint32_t const parentClose = parentCloseTime(env);
                    LoanParams const p{
                        .principal = units(ledger.f, c.principal),
                        .interestRate = c.interestRate,
                        .paymentInterval = c.paymentInterval,
                        .paymentTotal = 1,
                        .startDate = parentClose + 1'000,
                    };
                    auto const at = [&](char const* what, std::optional<std::int64_t> d) {
                        return d ? std::string{what} + std::to_string(*d) : std::string{};
                    };
                    std::string const text =
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)) +
                        stageText(c.stage) + loanText(p) + at(" restaged start P + ", c.start) +
                        at(" sub P + ", c.subscription) + at(" red P + ", c.redemption) + ": ";
                    OpenView view{*env.current()};
                    Keylet const loan = nextLoan(view, ledger.f);
                    if (!tryStage(*this, text, [&] {
                            stageInvestment(env, view, ledger.f, {});
                            TER const proposed = applyLoanSet(env, view, ledger.f, p).ter;
                            if (proposed != tesSUCCESS)
                                throw std::runtime_error("proposal " + transToken(proposed));
                            stageLending(env, view, ledger.f, c.stage);
                            Sandbox sb(&view, TapNone);
                            if (c.start)
                            {
                                auto const sle = sb.peek(loan);
                                sle->at(sfStartDate) =
                                    static_cast<std::uint32_t>(parentClose + *c.start);
                                sle->at(sfNextPaymentDueDate) =
                                    static_cast<std::uint32_t>(parentClose + *c.start) +
                                    sle->at(sfPaymentInterval);
                                sb.update(sle);
                            }
                            if (c.subscription)
                            {
                                auto const vault = sb.peek(ledger.f.vaultKeylet);
                                vault->at(sfSubscriptionDate) =
                                    static_cast<std::uint32_t>(parentClose + *c.subscription);
                                vault->at(sfRedemptionDate) =
                                    static_cast<std::uint32_t>(parentClose + c.redemption.value());
                                sb.update(vault);
                            }
                            sb.apply(view);
                        }))
                        continue;
                    checkAccept(env, ledger.f, view, loan, p, c.expected, text);
                }
            }
        };

        run("start date", s.iou, kAcceptStartDate);
        run("subscription date", s.iou, kAcceptSubscriptionDate);
        run("redemption date", s.iou, kAcceptRedemptionDate);
        run("open zone", s.all, kAcceptOpenZone);
    }

    void
    testLoanAcceptBoundaries(LendingSetup const& s)
    {
        runLoanAcceptBoundaries(s);
    }

    void
    runDelete(std::string const& label, LoanKind kind, TER expected, bool withOtherLoan = false)
    {
        using namespace jtx;
        testcase("LoanDelete: " + label);

        Env env{*this, lendingTestAmendments()};
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
        OpenView view{*env.current()};
        AppliedLoanTx const cpp = applyLoanDelete(env, view, f, loanKeylet, p, f.borrower);
        LeanDeleteTx const lean = leanLoanDelete(cpp);
        expectLawful(lean.can);
        expectSame(*this, label + ": ", cpp, lean, expected);
    }

    void
    runLoanDeleteBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanDeleteCase const> cases) {
            testcase("LoanDelete " + name);
            for (TestLedger const& ledger : ledgers)
            {
                for (std::size_t i = 0; LoanDeleteCase const& c : cases)
                {
                    jtx::Env& env = *ledger.env;
                    std::uint32_t const parentClose = parentCloseTime(env);
                    LoanParams p{
                        .principal = units(ledger.f, c.principal),
                        .interestRate = c.interestRate,
                        .paymentTotal = c.paymentTotal,
                    };
                    if (c.pending)
                        p.startDate = parentClose + 1'000;
                    jtx::Account const& by = c.by == DeleteParty::Owner ? ledger.f.owner
                        : c.by == DeleteParty::Other                    ? ledger.f.holder
                                                                        : ledger.f.borrower;
                    std::string const at =
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)) + by.name() +
                        " deletes" + loanText(p) + " debt " + std::to_string(c.debt) + " paid " +
                        std::to_string(c.paid) + (c.impaired ? " impaired" : "") +
                        (c.defaulted ? " defaulted" : "") + ": ";
                    OpenView view{*env.current()};
                    std::optional<Keylet> loan;
                    if (!tryStage(*this, at, [&] {
                            stageInvestment(env, view, ledger.f, {.debt = c.debt});
                            loan = createLoan(env, view, ledger.f, p);
                            for (std::uint32_t i = 0; i < c.paid; ++i)
                            {
                                Number const installment = view.read(*loan)->at(sfPeriodicPayment);
                                TER const ter = applyOn(
                                    env,
                                    view,
                                    jtx::loan::pay(
                                        ledger.f.borrower, loan->key, ledger.f.asset(installment)),
                                    jtx::Fee(env.current()->fees().base * 101));
                                if (ter != tesSUCCESS)
                                    throw std::runtime_error("payment " + transToken(ter));
                            }
                            if (c.impaired)
                            {
                                dueAt(view, *loan, parentClose, -1);
                                TER const ter = applyOn(
                                    env,
                                    view,
                                    jtx::loan::manage(ledger.f.owner, loan->key, tfLoanImpair));
                                if (ter != tesSUCCESS)
                                    throw std::runtime_error("impair " + transToken(ter));
                            }
                            if (c.defaulted)
                            {
                                dueAt(view, *loan, parentClose, -61);
                                TER const ter = applyOn(
                                    env,
                                    view,
                                    jtx::loan::manage(ledger.f.owner, loan->key, tfLoanDefault));
                                if (ter != tesSUCCESS)
                                    throw std::runtime_error("default " + transToken(ter));
                            }
                        }))
                        continue;
                    AppliedLoanTx const cpp = applyLoanDelete(env, view, ledger.f, *loan, p, by);
                    LeanDeleteTx const lean = leanLoanDelete(cpp);
                    expectSame(*this, at, cpp, lean, c.expected);
                }
            }
        };

        run("payments remaining", s.all, kDeleteRemaining);
        run("beside another loan", s.all, kDeleteBesideLoan);
        run("party", s.all, kDeleteParty);
        run("impaired", s.all, kDeleteImpaired);
    }

    void
    testLoanDeleteBoundaries(LendingSetup const& s)
    {
        runLoanDeleteBoundaries(s);
    }

    void
    runTests() override
    {
        jtx::Env iouEnv{*this, lendingTestAmendments()};
        jtx::Env mptEnv{*this, lendingTestAmendments()};
        LendingSetup const s = setUpLending(iouEnv, mptEnv);

        // A broker with `cover`, the vault staged into investment (and redemption).
        struct LoanSetRow
        {
            char const* label;
            LoanParams loan{};
            TER expected;
            Number cover{500};
            std::optional<Number> debtMaximum{};
            bool toInvestment = true;
            bool toRedemption = false;
            LendingAsset asset = LendingAsset::iou;
        };
        auto const loanSet = [&](LoanSetRow const& r) {
            runLoanSet(
                s,
                r.label,
                r.loan,
                r.expected,
                r.cover,
                r.debtMaximum,
                r.toInvestment,
                r.toRedemption,
                r.asset);
        };

        // One-step loans
        // clang-format off
        static LoanSetRow const kOneStepRows[] = {
            {.label = "one-step loan without interest", .expected = tesSUCCESS},
            {.label = "one-step loan with interest", .loan = {.interestRate = 10'000, .paymentTotal = 3}, .expected = tesSUCCESS},
            {.label = "one-step loan with fees", .loan = {.interestRate = 10'000, .originationFee = Number{5}, .serviceFee = Number{1}, .latePaymentFee = Number{2}, .closePaymentFee = Number{3}}, .expected = tesSUCCESS},
            {.label = "vault in the subscription phase", .expected = tecTOO_SOON, .toInvestment = false},
            {.label = "vault in the redemption phase", .expected = tecEXPIRED, .toRedemption = true},
            // Covered by testLoanSetBoundaries.
            {.label = "final payment too close to the redemption date", .loan = {.paymentInterval = 500'000}, .expected = tecNO_PERMISSION},
            // Covered by testLoanSetBoundaries.
            {.label = "principal above the vault's available assets", .loan = {.principal = Number{20'000}}, .expected = tecINSUFFICIENT_FUNDS, .cover = Number{5'000}},
            // Covered by testLoanSetBoundaries.
            {.label = "principal above the debt maximum", .expected = tecLIMIT_EXCEEDED, .debtMaximum = Number{500}},
            // Covered by testLoanSetBoundaries.
            {.label = "not enough cover", .expected = tecINSUFFICIENT_FUNDS, .cover = Number{0}},
            {.label = "fee off the vault grid", .loan = {.originationFee = Number{1, -7}}, .expected = tecPRECISION_LOSS},
            // One grid unit in three installments: the rounded-up installment covers the whole
            // loan in one payment, so the schedule cannot be honoured. Covered by
            // testLoanSetBoundaries.
            {.label = "principal too small for its installments", .loan = {.principal = Number{1, -6}, .paymentTotal = 3}, .expected = tecPRECISION_LOSS},
            {.label = "schedule past the protocol time limit", .loan = {.paymentInterval = 4'000'000'000}, .expected = tecKILLED},
            {.label = "grace period past the protocol time limit", .loan = {.paymentInterval = 0xFFFF'FFFF, .gracePeriod = 0xFFFF'FFFF}, .expected = tecKILLED},
            {.label = "interval past the protocol time limit", .loan = {.paymentInterval = 0xFFFF'FFFF}, .expected = tecKILLED},
            {.label = "installment count past the protocol time limit", .loan = {.paymentTotal = 0xFFFF'FFFF}, .expected = tecKILLED},
            {.label = "fee not representable as an amount", .loan = {.originationFee = Number{12'345'678'901'234'567LL, -16}}, .expected = tecPRECISION_LOSS},
            // A per-period rate below 1e-9 takes the binomial series.
            {.label = "tiny interest rate", .loan = {.principal = Number{5'000}, .interestRate = 10, .paymentInterval = 60}, .expected = tesSUCCESS},
            // A tiny rate over many installments (rate times count still below 1e-9): the binomial
            // series converges before its last term.
            {.label = "tiny interest rate over 50 installments", .loan = {.principal = Number{5'000}, .interestRate = 1, .paymentInterval = 60, .paymentTotal = 50}, .expected = tesSUCCESS},
        };
        // clang-format on
        for (LoanSetRow const& r : kOneStepRows)
            loanSet(r);
        testLoanInterestPastOpenLimit();
        testAcceptPastOpenLimit();
        testCoarsenedVaultRefusesLoan();

        // MPT vault
        // clang-format off
        static LoanSetRow const kMptRows[] = {
            {.label = "one-step loan with interest", .loan = {.interestRate = 10'000, .paymentTotal = 3}, .expected = tesSUCCESS, .asset = LendingAsset::mpt},
            {.label = "one-step loan with fees", .loan = {.interestRate = 10'000, .originationFee = Number{5}, .serviceFee = Number{1}, .latePaymentFee = Number{2}, .closePaymentFee = Number{3}}, .expected = tesSUCCESS, .asset = LendingAsset::mpt},
            {.label = "fee off the vault grid", .loan = {.originationFee = Number{5, -1}}, .expected = tecPRECISION_LOSS, .asset = LendingAsset::mpt},
            {.label = "principal above the MPT maximum", .loan = {.principal = Number{1, 19}}, .expected = tecPRECISION_LOSS, .asset = LendingAsset::mpt},
        };
        // clang-format on
        for (LoanSetRow const& r : kMptRows)
            loanSet(r);

        // Two-step proposals
        runTwoStep(s, "two-step proposal", 1'000, tesSUCCESS);
        runTwoStep(s, "two-step proposal with an expired start date", -10, tecEXPIRED);
        // Start dates are judged at the parent close time, not the ledger close time. Covered by
        // testLoanSetBoundaries.
        runTwoStep(s, "two-step proposal starting at the parent close time", 0, tecEXPIRED);
        runTwoStep(
            s, "two-step proposal starting one second after the parent close time", 1, tesSUCCESS);
        testLoanSetAtPhaseBoundary(false);
        testLoanSetAtPhaseBoundary(true);

        // LoanAccept
        runAccept("accept a pending proposal", true, 0, tesSUCCESS);
        runAccept(
            "accept a pending proposal with an origination fee", true, 0, tesSUCCESS, Number{5});
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

        testLoanSetBoundaries(s);
        testLoanAcceptBoundaries(s);
        testLoanDeleteBoundaries(s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanSet, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
