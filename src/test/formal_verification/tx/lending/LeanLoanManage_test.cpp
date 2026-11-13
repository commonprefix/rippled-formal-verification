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
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// A LoanManage `action` on a loan of `principal` units in `paymentTotal` installments, without
// interest unless `interestRate` is set, with the vault in its investment phase. A `debt` loan (one
// payment) is taken first; an `impaired` loan is impaired while due at P - 1 (P: the parent close
// time). The loan's next payment then falls due at P + `due`, and `cover` with the minimum cover
// rate `coverRate`, and the vault's `deployed` assets and unrealized `loss`, are staged after it.
struct LoanManageCase
{
    ManageAction action{};
    std::int64_t debt{};
    std::int64_t principal{};
    std::uint32_t interestRate{};
    std::uint32_t paymentInterval{600};
    std::uint32_t paymentTotal{2};
    std::optional<std::uint32_t> gracePeriod{};
    std::int64_t due{};
    std::int64_t cover{};
    std::uint32_t coverRate{};
    std::optional<std::int64_t> deployed{};
    std::int64_t loss{};
    TER expected;
    bool impaired{};
};

// Differential tests of LoanManage: impair, unimpair and default.
// Rows stage ledger state on a throwaway view, including states no transaction sequence may
// reach: a verdict compares model and C++ on the same pre-state, not a claim the state is
// reachable (see stageLending).
class LeanLoanManage_test : public LeanSuite
{
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

    // One LoanManage on `view`: C++ applies it there, the model runs on the same pre-state.
    void
    checkManage(
        jtx::Env& env,
        OpenView& view,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        ManageAction action,
        TER expected,
        std::string const& at = {})
    {
        AppliedLoanTx const cpp = applyLoanManage(env, view, f, loanKeylet, p, action);
        expectSame(*this, at, cpp, leanLoanManage(cpp, action), expected);
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
        if (!tryStage(
                *this,
                label,
                [&] { staged = stageLoan(env, view, f, p, kind, parentCloseTime(env), delay); }) ||
            !staged)
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
        checkManage(env, view, f, loanKeylet, p, action, expected);
    }

    // Each row stages the asset's shared ledger on a throwaway view: the vault in its investment
    // phase, the broker's management fee at 1% and no cover rate, the row's debt loan, the loan,
    // then its due date, cover, cover rate (with a 20% liquidation rate) and vault fields. The
    // row's LoanManage must give its verdict on both sides, with every field of the loan, its
    // broker and the pool, and the amount moved into the pool, equal when both succeed. Amounts
    // are in units of the vault grid.
    // - Default deadline: a default needs P past due date + grace period (exclusive), else
    //   tecTOO_SOON. Each cusp puts that deadline on P.
    // - Impair due date: an impairment needs P past the due date (exclusive), else tecTOO_SOON.
    // - Impair loss cap: an impairment adds the principal to the vault's unrealized loss; past the
    //   deployed assets it is tecLIMIT_EXCEEDED. Each cusp sits at loss + principal == deployed.
    // - Default cover at the principal / at the cover available: a default moves
    //   min(min(minimum cover * 20%, principal), cover) into the vault, with minimum cover
    //   (debt + principal) * rate / 1e5. Each cusp puts the liquidation share exactly on the
    //   principal, or on the cover; the verdict does not change.
    // - Default with interest: at 100% a year over 31'536'000 s (periodic rate 1) a principal of
    //   3'153'600'000 in two installments carries a total value of 8'409'600'000 and a 1%
    //   management fee of 52'560'000; the default removes the scheduled interest 5'203'440'000
    //   from the vault's yield and, on an impaired loan, releases the 3'153'600'000 loss.
    // - Default cover with interest: 20% of the minimum cover 3'153'600'000 x 100%, 630'720'000,
    //   leaves the broker's pseudo-account for the vault, or the whole cover when less; for a
    //   principal of 3 the 0.6 share truncates to nothing.
    // - Impair with interest: the loss booked is the principal 3'153'600'000, not the interest.
    // - Unimpair: a loan that is not impaired is tecNO_PERMISSION; an impaired loan is unimpaired,
    //   its loss released, whatever its due date.
    // The date rules (exclusive deadlines, impairment only of a late loan, no due-date change on
    // impair or unimpair) are those of fixCleanup3_4_0.
    // clang-format off
    static constexpr LoanManageCase kDefaultDeadline[] = {
        // interval 600, grace 60 ends at P
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 60, .due = -62, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 60, .due = -61, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 60, .due = -60, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 60, .due = -59, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 60, .due = -58, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 61, .due = -62, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 61, .due = -61, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 61, .due = -60, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 61, .due = -59, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 61, .due = -58, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 62, .due = -62, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 62, .due = -61, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 62, .due = -60, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 62, .due = -59, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 62, .due = -58, .expected = tecTOO_SOON},
        // interval 600, grace 600 ends at P
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 598, .due = -602, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 598, .due = -601, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 598, .due = -600, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 598, .due = -599, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 598, .due = -598, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 599, .due = -602, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 599, .due = -601, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 599, .due = -600, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 599, .due = -599, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 599, .due = -598, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 600, .due = -602, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 600, .due = -601, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 600, .due = -600, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 600, .due = -599, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .gracePeriod = 600, .due = -598, .expected = tecTOO_SOON},
        // interval 2'592'000, grace 86'400 ends at P
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'398, .due = -86'402, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'398, .due = -86'401, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'398, .due = -86'400, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'398, .due = -86'399, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'398, .due = -86'398, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'399, .due = -86'402, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'399, .due = -86'401, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'399, .due = -86'400, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'399, .due = -86'399, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'399, .due = -86'398, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'400, .due = -86'402, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'400, .due = -86'401, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'400, .due = -86'400, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'400, .due = -86'399, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'400, .due = -86'398, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'401, .due = -86'402, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'401, .due = -86'401, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'401, .due = -86'400, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'401, .due = -86'399, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'401, .due = -86'398, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'402, .due = -86'402, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'402, .due = -86'401, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'402, .due = -86'400, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'402, .due = -86'399, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 86'402, .due = -86'398, .expected = tecTOO_SOON},
        // interval 2'592'000, grace 2'592'000 ends at P
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'998, .due = -2'592'002, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'998, .due = -2'592'001, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'998, .due = -2'592'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'998, .due = -2'591'999, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'998, .due = -2'591'998, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'999, .due = -2'592'002, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'999, .due = -2'592'001, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'999, .due = -2'592'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'999, .due = -2'591'999, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'591'999, .due = -2'591'998, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'592'000, .due = -2'592'002, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'592'000, .due = -2'592'001, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'592'000, .due = -2'592'000, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'592'000, .due = -2'591'999, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 1'000'000'000, .paymentInterval = 2'592'000, .gracePeriod = 2'592'000, .due = -2'591'998, .expected = tecTOO_SOON},
    };
    static constexpr LoanManageCase kImpairDueDate[] = {
        // due at P
        {.action = ManageAction::impair, .principal = 1'000'000'000, .due = -2, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .due = -1, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .due = 0, .expected = tecTOO_SOON},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .due = 1, .expected = tecTOO_SOON},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .due = 2, .expected = tecTOO_SOON},
    };
    static constexpr LoanManageCase kImpairLossCap[] = {
        // loss 0 + principal 1 = deployed 1
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 0, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 2, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 3, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1, .loss = 1, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 2, .loss = 1, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 3, .loss = 1, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 2, .loss = 2, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 3, .loss = 2, .expected = tesSUCCESS},
        // loss 999'999'999 + principal 1 = deployed 1'000'000'000
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 999'999'997, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 999'999'997, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 999'999'997, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 999'999'997, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 999'999'997, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 999'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 999'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 999'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 999'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 999'999'999, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 999'999'999, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 999'999'999, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 1'000'000'000, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 1'000'000'000, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 1'000'000'001, .expected = tesSUCCESS},
        // loss 0 + principal 1'000'000'000 = deployed 1'000'000'000
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 1, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 1, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 1, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 1, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 1, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 2, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 2, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 2, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 2, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 1'000'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 2, .expected = tesSUCCESS},
        // loss 500'000'000 + principal 500'000'000 = deployed 1'000'000'000
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 499'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 499'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 499'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 499'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 499'999'998, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 499'999'999, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 499'999'999, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 499'999'999, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 499'999'999, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 499'999'999, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 500'000'000, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 500'000'000, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 500'000'000, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 500'000'000, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 500'000'000, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 500'000'001, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 500'000'001, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'998, .loss = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 999'999'999, .loss = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'000, .loss = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'001, .loss = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 500'000'000, .paymentTotal = 1, .due = -1, .deployed = 1'000'000'002, .loss = 500'000'002, .expected = tesSUCCESS},
    };
    static constexpr LoanManageCase kDefaultCoverAtPrincipal[] = {
        // (debt 16 + principal 4) x 100'000 / 5e5 = principal
        {.action = ManageAction::defaultLoan, .debt = 14, .principal = 2, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 14, .principal = 3, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 14, .principal = 4, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 14, .principal = 5, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 14, .principal = 6, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 15, .principal = 2, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 15, .principal = 3, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 15, .principal = 4, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 15, .principal = 5, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 15, .principal = 6, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 16, .principal = 2, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 16, .principal = 3, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 16, .principal = 4, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 16, .principal = 5, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 16, .principal = 6, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 17, .principal = 2, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 17, .principal = 3, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 17, .principal = 4, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 17, .principal = 5, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 17, .principal = 6, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 18, .principal = 2, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 18, .principal = 3, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 18, .principal = 4, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 18, .principal = 5, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 18, .principal = 6, .due = -61, .cover = 20, .coverRate = 100'000, .expected = tesSUCCESS},
        // (debt 400'000'000 + principal 100'000'000) x 100'000 / 5e5 = principal
        {.action = ManageAction::defaultLoan, .debt = 399'999'998, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'998, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'998, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'998, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'998, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'999, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'999, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'999, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'999, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 399'999'999, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'000, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'000, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'000, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'000, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'000, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'001, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'001, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'001, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'001, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'001, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'002, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'002, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'002, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'002, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 400'000'002, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 100'000, .expected = tesSUCCESS},
        // (debt 900'000'000 + principal 100'000'000) x 50'000 / 5e5 = principal
        {.action = ManageAction::defaultLoan, .debt = 899'999'998, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'998, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'998, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'998, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'998, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'999, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'999, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'999, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'999, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 899'999'999, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'000, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'000, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'000, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'000, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'000, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'001, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'001, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'001, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'001, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'001, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'002, .principal = 99'999'998, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'002, .principal = 99'999'999, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'002, .principal = 100'000'000, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'002, .principal = 100'000'001, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 900'000'002, .principal = 100'000'002, .due = -61, .cover = 200'000'010, .coverRate = 50'000, .expected = tesSUCCESS},
    };
    static constexpr LoanManageCase kDefaultCoverAtAvailable[] = {
        // (debt 0 + principal 5) x 100'000 / 5e5 = cover 1
        {.action = ManageAction::defaultLoan, .principal = 5, .due = -61, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 5, .due = -61, .cover = 1, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 5, .due = -61, .cover = 2, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 5, .due = -61, .cover = 3, .coverRate = 100'000, .expected = tesSUCCESS},
        // (debt 0 + principal 500'000) x 1 / 5e5 = cover 1
        {.action = ManageAction::defaultLoan, .principal = 500'000, .due = -61, .coverRate = 1, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 500'000, .due = -61, .cover = 1, .coverRate = 1, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 500'000, .due = -61, .cover = 2, .coverRate = 1, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 500'000, .due = -61, .cover = 3, .coverRate = 1, .expected = tesSUCCESS},
        // (debt 0 + principal 5'000'000'000) x 10'000 / 5e5 = cover 100'000'000
        {.action = ManageAction::defaultLoan, .principal = 5'000'000'000, .due = -61, .cover = 99'999'998, .coverRate = 10'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 5'000'000'000, .due = -61, .cover = 99'999'999, .coverRate = 10'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 5'000'000'000, .due = -61, .cover = 100'000'000, .coverRate = 10'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 5'000'000'000, .due = -61, .cover = 100'000'001, .coverRate = 10'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 5'000'000'000, .due = -61, .cover = 100'000'002, .coverRate = 10'000, .expected = tesSUCCESS},
        // (debt 1'000'000'000 + principal 1'000'000'000) x 100'000 / 5e5 = cover 400'000'000
        {.action = ManageAction::defaultLoan, .debt = 1'000'000'000, .principal = 1'000'000'000, .due = -61, .cover = 399'999'998, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 1'000'000'000, .principal = 1'000'000'000, .due = -61, .cover = 399'999'999, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 1'000'000'000, .principal = 1'000'000'000, .due = -61, .cover = 400'000'000, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 1'000'000'000, .principal = 1'000'000'000, .due = -61, .cover = 400'000'001, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .debt = 1'000'000'000, .principal = 1'000'000'000, .due = -61, .cover = 400'000'002, .coverRate = 100'000, .expected = tesSUCCESS},
    };
    static constexpr LoanManageCase kDefaultWithInterest[] = {
        // grace 60 ends at P, 100% a year over 31'536'000 s: interest 3'153'600'000 then 1'051'200'000
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -62, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -61, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -60, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -59, .expected = tecTOO_SOON},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -58, .expected = tecTOO_SOON},
        // the same, impaired: the unrealized loss is released
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -62, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -61, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -60, .expected = tecTOO_SOON, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -59, .expected = tecTOO_SOON, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -58, .expected = tecTOO_SOON, .impaired = true},
        // principal 3 at the same rate: interest 3 then 1
        {.action = ManageAction::defaultLoan, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -61, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .gracePeriod = 60, .due = -60, .expected = tecTOO_SOON},
    };
    static constexpr LoanManageCase kDefaultCoverWithInterest[] = {
        // (debt 0 + principal 3'153'600'000) x 100'000 / 5e5 = cover 630'720'000
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'719'998, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'719'999, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'720'000, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'720'001, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'720'002, .coverRate = 100'000, .expected = tesSUCCESS},
        // the same, impaired
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'719'998, .coverRate = 100'000, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'719'999, .coverRate = 100'000, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'720'000, .coverRate = 100'000, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'720'001, .coverRate = 100'000, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::defaultLoan, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 630'720'002, .coverRate = 100'000, .expected = tesSUCCESS, .impaired = true},
        // (debt 0 + principal 3) x 100'000 / 5e5 = cover 0.6
        {.action = ManageAction::defaultLoan, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 1, .coverRate = 100'000, .expected = tesSUCCESS},
        {.action = ManageAction::defaultLoan, .principal = 3, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -61, .cover = 2, .coverRate = 100'000, .expected = tesSUCCESS},
    };
    static constexpr LoanManageCase kImpairWithInterest[] = {
        // due at P
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -2, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -1, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = 0, .expected = tecTOO_SOON},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = 1, .expected = tecTOO_SOON},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = 2, .expected = tecTOO_SOON},
        // loss 0 + principal 3'153'600'000 = deployed 3'153'600'000
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -1, .deployed = 3'153'599'998, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -1, .deployed = 3'153'599'999, .expected = tecLIMIT_EXCEEDED},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -1, .deployed = 3'153'600'000, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -1, .deployed = 3'153'600'001, .expected = tesSUCCESS},
        {.action = ManageAction::impair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -1, .deployed = 3'153'600'002, .expected = tesSUCCESS},
    };
    static constexpr LoanManageCase kUnimpair[] = {
        // not impaired, due on either side of P
        {.action = ManageAction::unimpair, .principal = 1'000'000'000, .due = -1, .expected = tecNO_PERMISSION},
        {.action = ManageAction::unimpair, .principal = 1'000'000'000, .due = 1, .expected = tecNO_PERMISSION},
        // impaired, then due at P
        {.action = ManageAction::unimpair, .principal = 1'000'000'000, .due = -2, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 1'000'000'000, .due = -1, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 1'000'000'000, .due = 0, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 1'000'000'000, .due = 1, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 1'000'000'000, .due = 2, .expected = tesSUCCESS, .impaired = true},
        // impaired with interest, then due at P
        {.action = ManageAction::unimpair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -2, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = -1, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = 0, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = 1, .expected = tesSUCCESS, .impaired = true},
        {.action = ManageAction::unimpair, .principal = 3'153'600'000, .interestRate = 100'000, .paymentInterval = 31'536'000, .due = 2, .expected = tesSUCCESS, .impaired = true},
    };
    // clang-format on
    void
    runLoanManageBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanManageCase const> cases) {
            for (TestLedger const& l : ledgers)
            {
                beginCase(
                    ("LoanManage " + vaultName(*l.env, l.f.vaultKeylet) + " " + name).c_str());
                for (LoanManageCase const& c : cases)
                {
                    jtx::Env& env = *l.env;
                    std::uint32_t const pct = parentCloseTime(env);
                    LoanParams const p{
                        .principal = units(l.f, c.principal),
                        .interestRate = c.interestRate,
                        .paymentInterval = c.paymentInterval,
                        .paymentTotal = c.paymentTotal,
                        .gracePeriod = c.gracePeriod,
                    };
                    std::string at = actionName(c.action) + " of" + loanText(p) + " due P + " +
                        std::to_string(c.due) + " debt " + std::to_string(c.debt) + " cover " +
                        std::to_string(c.cover) + " rate " + std::to_string(c.coverRate);
                    if (c.deployed)
                    {
                        at += " deployed " + std::to_string(*c.deployed) + " loss " +
                            std::to_string(c.loss);
                    }
                    if (c.impaired)
                        at += " impaired";
                    at += ": ";
                    OpenView view{*env.current()};
                    std::optional<Keylet> loan;
                    if (!tryStage(*this, at, [&] {
                            stageInvestment(
                                env, view, l.f, {.debt = c.debt, .managementFeeRate = 1'000});
                            loan = createLoan(env, view, l.f, p);
                            if (c.impaired)
                            {
                                dueAt(view, *loan, pct, -1);
                                TER const ter = applyOn(
                                    env,
                                    view,
                                    jtx::loan::manage(l.f.owner, loan->key, tfLoanImpair));
                                if (ter != tesSUCCESS)
                                    throw std::runtime_error("impair " + transToken(ter));
                            }
                            dueAt(view, *loan, pct, c.due);
                            stageLending(
                                env, view, l.f, {.cover = c.cover, .coverRate = c.coverRate});
                            if (c.deployed)
                            {
                                stageDeployed(
                                    view,
                                    l.f.vaultKeylet,
                                    units(l.f, *c.deployed),
                                    units(l.f, c.loss));
                            }
                        }))
                        continue;
                    AppliedLoanTx const cpp = applyLoanManage(env, view, l.f, *loan, p, c.action);
                    LeanLoanTx const lean = leanLoanManage(cpp, c.action);
                    expectSame(*this, at, cpp, lean, c.expected);
                }
            }
        };

        run("default deadline", s.all, kDefaultDeadline);
        run("impair due date", s.all, kImpairDueDate);
        run("impair loss cap", s.all, kImpairLossCap);
        run("default cover at the principal", s.all, kDefaultCoverAtPrincipal);
        run("default cover at the cover available", s.all, kDefaultCoverAtAvailable);
        run("default with interest", s.all, kDefaultWithInterest);
        run("default cover with interest", s.all, kDefaultCoverWithInterest);
        run("impair with interest", s.all, kImpairWithInterest);
        run("unimpair", s.all, kUnimpair);
    }

    void
    testLoanManageBoundaries(LendingSetup const& s)
    {
        runLoanManageBoundaries(s);
    }

    // The single-value tests' fixtures: the default broker with 500 of cover, one per asset, and
    // an IOU broker without cover rates or cover. Each test runs on a throwaway view of one.
    struct Setup
    {
        BrokerFixture iou;
        BrokerFixture mpt;
        BrokerFixture uncovered;
    };

    static Setup
    setup(jtx::Env& env, jtx::Env& mptEnv, jtx::Env& uncoveredEnv)
    {
        auto const iou = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, iou, Number{500});
        auto const mpt = setUpBrokerVault(
            mptEnv, BrokerConfig{}, Number{10'000}, false, true, LendingAsset::mpt);
        depositCover(mptEnv, mpt, Number{500});
        // Loans are aged by moving their dates back; keep those dates well above zero.
        env.close(env.now() + std::chrono::seconds{10'000});
        mptEnv.close(mptEnv.now() + std::chrono::seconds{10'000});
        auto const uncovered = setUpBrokerVault(
            uncoveredEnv,
            BrokerConfig{.coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt});
        uncoveredEnv.close(uncoveredEnv.now() + std::chrono::seconds{10'000});
        return {.iou = iou, .mpt = mpt, .uncovered = uncovered};
    }

    void
    runTests() override
    {
        jtx::Env env{*this, lendingTestAmendments()};
        jtx::Env mptEnv{*this, lendingTestAmendments()};
        jtx::Env uncoveredEnv{*this, lendingTestAmendments()};
        Setup const fx = setup(env, mptEnv, uncoveredEnv);
        BrokerFixture const& iou = fx.iou;
        BrokerFixture const& mpt = fx.mpt;
        jtx::Env iouLendingEnv{*this, lendingTestAmendments()};
        jtx::Env mptLendingEnv{*this, lendingTestAmendments()};
        LendingSetup const s = setUpLending(iouLendingEnv, mptLendingEnv);

        struct ManageTest
        {
            char const* name;
            std::uint32_t loanAge{};
            bool impairFirst = false;
            ManageAction action;
            TER expected;
            LoanKind kind = LoanKind::active;
        };
        auto const manage = [&](jtx::Env& e, BrokerFixture const& f, ManageTest const& t) {
            runManage(e, f, t.name, t.loanAge, t.impairFirst, t.action, t.expected, t.kind);
        };

        // clang-format off
        static ManageTest const kIouTests[] = {
            // The first installment is due 600 s after the start, with a 60 s grace period.
            {.name = "a late loan", .loanAge = 601, .action = ManageAction::impair, .expected = tesSUCCESS},
            // Covered by testLoanManageBoundaries.
            {.name = "a loan that is not late", .action = ManageAction::impair, .expected = tecTOO_SOON},
            {.name = "an impaired loan", .loanAge = 601, .impairFirst = true, .action = ManageAction::impair, .expected = tecNO_PERMISSION},

            {.name = "an impaired loan", .loanAge = 601, .impairFirst = true, .action = ManageAction::unimpair, .expected = tesSUCCESS},
            {.name = "a loan that is not impaired", .action = ManageAction::unimpair, .expected = tecNO_PERMISSION},

            // Covered by testLoanManageBoundaries.
            {.name = "before the grace period ends", .loanAge = 601, .action = ManageAction::defaultLoan, .expected = tecTOO_SOON},
            {.name = "after the grace period", .loanAge = 700, .action = ManageAction::defaultLoan, .expected = tesSUCCESS},
            {.name = "an impaired loan after the grace period", .loanAge = 700, .impairFirst = true, .action = ManageAction::defaultLoan, .expected = tesSUCCESS},
        };
        static ManageTest const kMptTests[] = {
            {.name = "an MPT loan after the grace period", .loanAge = 700, .action = ManageAction::defaultLoan, .expected = tesSUCCESS},
            {.name = "an impaired MPT loan after the grace period", .loanAge = 700, .impairFirst = true, .action = ManageAction::defaultLoan, .expected = tesSUCCESS},
        };
        // clang-format on
        for (ManageTest const& t : kIouTests)
            manage(env, iou, t);
        for (ManageTest const& t : kMptTests)
            manage(mptEnv, mpt, t);
        // clang-format off
        manage(uncoveredEnv, fx.uncovered, {.name = "a broker without cover", .loanAge = 700, .action = ManageAction::defaultLoan, .expected = tesSUCCESS});

        // Loans that cannot be managed at all
        static ManageTest const kUnmanageableTests[] = {
            {.name = "a pending proposal", .action = ManageAction::impair, .expected = tecNO_PERMISSION, .kind = LoanKind::pending},
            {.name = "a defaulted loan", .loanAge = 700, .action = ManageAction::impair, .expected = tecNO_PERMISSION, .kind = LoanKind::defaulted},
            {.name = "a paid-off loan", .action = ManageAction::impair, .expected = tecNO_PERMISSION, .kind = LoanKind::paidOff},
        };
        // clang-format on
        for (ManageTest const& t : kUnmanageableTests)
            manage(env, iou, t);
        testLoanManageBoundaries(s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanManage, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
