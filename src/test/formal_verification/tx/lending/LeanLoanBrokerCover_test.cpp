#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
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

#include <cstddef>
#include <cstdint>
#include <exception>
#include <optional>
#include <span>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// A cover deposit by the owner of amount * 10^exponent vault grid units, on a broker staged as
// `stage`.
struct LoanBrokerCoverDepositCase
{
    LendingStage stage{};
    std::int64_t amount{};
    // The amount is amount * 10^exponent vault grid units.
    int exponent{};
    TER expected;
};

// A cover withdrawal by the owner, as LoanBrokerCoverDepositCase.
struct LoanBrokerCoverWithdrawCase
{
    LendingStage stage{};
    std::int64_t amount{};
    // The amount is amount * 10^exponent vault grid units.
    int exponent{};
    TER expected;
};

// A cover clawback by the issuer, as LoanBrokerCoverDepositCase; without an amount it claws
// everything above the minimum cover.
struct LoanBrokerCoverClawbackCase
{
    LendingStage stage{};
    std::optional<std::int64_t> amount{};
    // The amount is amount * 10^exponent vault grid units.
    int exponent{};
    TER expected;
};

// Differential tests of the broker cover transactions: LoanBrokerCoverDeposit, CoverWithdraw and
// CoverClawback. Each compares preclaim (the `can*` TER), doApply (the TER and the broker's
// post-state) and the amount moved.
// Rows stage ledger state on a throwaway view, including states no transaction sequence may
// reach: a verdict compares model and C++ on the same pre-state, not a claim the state is
// reachable (see stageLending).
class LeanLoanBrokerCover_test : public LeanSuite
{
    static std::string
    opName(CoverOp op)
    {
        switch (op)
        {
            case CoverOp::Deposit:
                return "cover deposit";
            case CoverOp::Withdraw:
                return "cover withdraw";
            case CoverOp::Clawback:
                return "cover clawback";
        }
        return "?";
    }

    // Stage `stage` (the vault in its investment phase) on a throwaway view of the shared ledger,
    // run the cover transaction there and the model on the same pre-state.
    AppliedBrokerTx
    checkCover(
        TestLedger const& l,
        LendingStage const& stage,
        CoverOp op,
        std::optional<Number> const& amount,
        TER expected,
        std::string const& row = {})
    {
        std::optional<STAmount> const stAmount =
            amount ? std::optional<STAmount>{l.f.asset(*amount)} : std::nullopt;
        std::string const at = row + opName(op) + " " + stageText(stage) + " amount " +
            (amount ? to_string(*amount) : std::string{"none"}) + ": ";
        OpenView view{*l.env->current()};
        stageInvestment(*l.env, view, l.f, stage);
        AppliedBrokerTx const cpp = applyLoanBrokerCover(*l.env, view, l.f, op, stAmount);
        LeanBrokerTx const lean = leanLoanBrokerCover(cpp, op, stAmount);
        expectSame(*this, at, cpp, lean, expected);
        return cpp;
    }

    // A broker with `cover` deposited and, with `withLoan`, a loan of 1000 (minimum cover 100 at
    // the 10% rate), staged on the shared ledger of the asset like the default fixture broker
    // (1% management fee, 10% / 20% cover rates). `expectedMoved` is the cover both sides move.
    void
    runCover(
        LendingSetup const& s,
        std::string const& label,
        CoverOp op,
        Number const& cover,
        bool withLoan,
        std::optional<Number> const& amount,
        TER expected,
        std::optional<Number> const& expectedMoved = std::nullopt,
        LendingAsset assetKind = LendingAsset::iou)
    {
        testcase(opName(op) + ": " + label);
        TestLedger const& l = assetKind == LendingAsset::mpt ? s.mptLedger : s.iouLedger;
        ReadView const& view = *l.env->current();
        LendingStage stage{
            .cover = toUnits(view, l.f, cover),
            .managementFeeRate = 1'000,
            .coverRate = 10'000,
        };
        if (withLoan)
            stage.debt = toUnits(view, l.f, Number{1'000});
        AppliedBrokerTx const cpp = checkCover(l, stage, op, amount, expected);
        if (expectedMoved && cpp.ter == tesSUCCESS)
        {
            BEAST_EXPECTS(
                cpp.booked == *expectedMoved,
                "moved " + to_string(cpp.booked.value_or(Number{})) + " expected " +
                    to_string(*expectedMoved));
        }
    }

    // Each row stages the asset's shared ledger on a throwaway view (the vault in its investment
    // phase), applies the cover transaction there and expects its verdict on both sides, with
    // every broker field, the untouched vault and the cover moved equal when both succeed. Amounts
    // are in units of the vault grid (IOU scale 6: 1e-6, MPT: 1); a one-unit amount is written as
    // a 16-digit mantissa at exponent -15, so moving the mantissa leaves the grid.
    // A group comment names a boundary value (the cusp); its rows step those values around it.
    // - Deposit sub-grid (IOU): a deposit that truncates to zero grid units is tecPRECISION_LOSS.
    // - Deposit truncation (IOU): above one unit an off-grid deposit is truncated to the grid
    //   (10^9 units, or one unit less below it); the verdict does not change.
    // - Deposit open limit: cover + amount past 9e15 units is tecLIMIT_EXCEEDED. Each cusp puts
    //   cover + amount exactly on the limit.
    // - Withdraw sub-grid (IOU): as for a deposit.
    // - Withdraw all: withdrawing more than the cover is tecINSUFFICIENT_FUNDS. Each cusp
    //   withdraws the whole cover of a broker without debt.
    // - Withdraw minimum cover: leaving less than the minimum cover ceil(debt * rate / 1e5) is
    //   tecINSUFFICIENT_FUNDS. Each cusp leaves exactly the minimum.
    // - Clawback sub-grid (IOU): as for a deposit.
    // - Clawback no excess: a clawback without an amount and no cover above the minimum cover is
    //   tecINSUFFICIENT_FUNDS; one unit of excess is clawed. Each cusp holds exactly the minimum.
    // - Clawback clamp: a clawback above the excess over the minimum cover is clamped to it. The
    //   list reruns the withdraw minimum cover rows: an amount above the excess, which a withdrawal
    //   refuses, is clamped and succeeds, and with no excess the clawback is still
    //   tecINSUFFICIENT_FUNDS. Each cusp claws exactly the excess.
    // clang-format off
    static constexpr LoanBrokerCoverDepositCase kCoverDepositSubGrid[] = {
        // cover 0, one unit
        {.stage = {}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 2}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        // cover 1'000'000'000, one unit
        {.stage = {.cover = 999'999'998}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'998}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        // cover 8'999'999'999'999'997, one unit
        {.stage = {.cover = 8'999'999'999'999'995}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'995}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'995}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'995}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'995}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerCoverDepositCase kCoverDepositTruncation[] = {
        // one step of 1e9 units
        {.amount = 999'999'999'999'998, .exponent = -6, .expected = tesSUCCESS},
        {.amount = 999'999'999'999'999, .exponent = -6, .expected = tesSUCCESS},
        {.amount = 1'000'000'000'000'000, .exponent = -6, .expected = tesSUCCESS},
        {.amount = 1'000'000'000'000'001, .exponent = -6, .expected = tesSUCCESS},
        {.amount = 1'000'000'000'000'002, .exponent = -6, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerCoverDepositCase kCoverDepositOpenLimit[] = {
        // cover 0 + amount 9'000'000'000'000'000 = 9e15
        {.stage = {}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {}, .amount = 8'999'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {}, .amount = 9'000'000'000'000'000, .expected = tesSUCCESS},
        {.stage = {}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {}, .amount = 9'000'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 8'999'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1}, .amount = 9'000'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 2}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 8'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 2}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 2}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 2}, .amount = 9'000'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        // cover 1 + amount 8'999'999'999'999'999 = 9e15
        {.stage = {}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {}, .amount = 8'999'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {}, .amount = 9'000'000'000'000'000, .expected = tesSUCCESS},
        {.stage = {}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 8'999'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 2}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 8'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 2}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 2}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 3}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 8'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 3}, .amount = 8'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 3}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 3}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        // cover 8'999'999'999'999'999 + amount 1 = 9e15
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        // cover 4'500'000'000'000'000 + amount 4'500'000'000'000'000 = 9e15
        {.stage = {.cover = 4'499'999'999'999'998}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'998}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'998}, .amount = 4'500'000'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'998}, .amount = 4'500'000'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'998}, .amount = 4'500'000'000'000'002, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'999}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'999}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'999}, .amount = 4'500'000'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'999}, .amount = 4'500'000'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 4'499'999'999'999'999}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'000}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 4'500'000'000'000'000}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 4'500'000'000'000'000}, .amount = 4'500'000'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 4'500'000'000'000'000}, .amount = 4'500'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'000}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'001}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 4'500'000'000'000'001}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 4'500'000'000'000'001}, .amount = 4'500'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'001}, .amount = 4'500'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'001}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'002}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 4'500'000'000'000'002}, .amount = 4'499'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'002}, .amount = 4'500'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'002}, .amount = 4'500'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 4'500'000'000'000'002}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        // cover 1'000'000'000 + amount 8'999'999'000'000'000 = 9e15
        {.stage = {.cover = 999'999'998}, .amount = 8'999'998'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 8'999'998'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 8'999'999'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 8'999'999'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 8'999'999'000'000'002, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 8'999'998'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 8'999'998'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 8'999'999'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 8'999'999'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 8'999'999'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'000}, .amount = 8'999'998'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 8'999'998'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 8'999'999'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 8'999'999'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'000}, .amount = 8'999'999'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'001}, .amount = 8'999'998'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 8'999'998'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 8'999'999'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'001}, .amount = 8'999'999'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'001}, .amount = 8'999'999'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'002}, .amount = 8'999'998'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 8'999'998'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'002}, .amount = 8'999'999'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'002}, .amount = 8'999'999'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.cover = 1'000'000'002}, .amount = 8'999'999'000'000'002, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr LoanBrokerCoverWithdrawCase kCoverWithdrawSubGrid[] = {
        // cover 1, one unit
        {.stage = {}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 2}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 3}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 3}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        // cover 1'000'000'000, one unit
        {.stage = {.cover = 999'999'998}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'998}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        // cover 8'999'999'999'999'998, one unit
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerCoverWithdrawCase kCoverWithdrawAll[] = {
        // cover 1, amount 1
        {.stage = {}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 2}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 3}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 3, .expected = tesSUCCESS},
        // cover 1'000'000'000, amount 1'000'000'000
        {.stage = {.cover = 999'999'998}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // cover 8'999'999'999'999'998, amount 8'999'999'999'999'998
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 8'999'999'999'999'996, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 8'999'999'999'999'997, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 8'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 8'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 9'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 8'999'999'999'999'996, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 8'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 8'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 9'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 8'999'999'999'999'996, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 8'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 9'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 8'999'999'999'999'996, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 8'999'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 9'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 8'999'999'999'999'996, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 8'999'999'999'999'999, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 9'000'000'000'000'000, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerCoverWithdrawCase kCoverWithdrawMinimum[] = {
        // debt 1, rate 1, cover 2, amount 1
        {.stage = {.debt = 1, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 3, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 3, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 3, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 4, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 4, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 4, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        // debt 100'000, rate 1, cover 2, amount 1
        {.stage = {.debt = 100'000, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 1, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 1, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 1, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 2, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 2, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 2, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 3, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 3, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 3, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 4, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 4, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 4, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 10'000, cover 100'000'001, amount 1
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'003, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'003, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'003, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 10'000, cover 1'000'000'000, amount 900'000'000
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 899'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 900'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 900'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 900'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 900'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 900'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 900'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 900'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 900'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 900'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 900'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 900'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 900'000'002, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 10'000, cover 200'000'000, amount 100'000'000
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 99'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 100'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 100'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 100'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 100'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 100'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 100'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 100'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 100'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 100'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 100'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 100'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 100'000'002, .expected = tesSUCCESS},
        // debt 1'000'000'001, rate 10'000, cover 100'000'002, amount 1
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'003, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'003, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'003, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'004, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'004, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'004, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 1, cover 1'000'010'000, amount 1'000'000'000
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 100'000, cover 1'000'000'001, amount 1
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 100'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 100'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 100'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 100'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 100'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 100'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 100'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 100'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 100'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 100'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 100'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 100'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'003, .coverRate = 100'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'003, .coverRate = 100'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'003, .coverRate = 100'000}, .amount = 3, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerCoverClawbackCase kCoverClawbackSubGrid[] = {
        // cover 1, one unit
        {.stage = {}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 2}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 2}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 3}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 3}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 3}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        // cover 1'000'000'000, one unit
        {.stage = {.cover = 999'999'998}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'998}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'998}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'999}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 999'999'999}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'000}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'000}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'001}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'001}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'002}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 1'000'000'002}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        // cover 8'999'999'999'999'998, one unit
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'996}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'997}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'998}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 8'999'999'999'999'999}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 1'000'000'000'000'001, .exponent = -15, .expected = tesSUCCESS},
        {.stage = {.cover = 9'000'000'000'000'000}, .amount = 1'000'000'000'000'002, .exponent = -15, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerCoverClawbackCase kCoverClawbackNoExcess[] = {
        // debt 0, rate 1, cover 0
        {.stage = {.coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 2, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        // debt 1, rate 1, cover 1
        {.stage = {.coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 3, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 1, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 2, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 3, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 2, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 3, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 2, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 3, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        // debt 100'000, rate 1, cover 1
        {.stage = {.debt = 99'998, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 99'999, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'001, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'002, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 99'998, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 99'999, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'001, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'002, .cover = 1, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 99'998, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 99'999, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 2, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 100'001, .cover = 2, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'002, .cover = 2, .coverRate = 1}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 99'998, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 99'999, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 100'001, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        {.stage = {.debt = 100'002, .cover = 3, .coverRate = 1}, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 10'000, cover 100'000'000
        {.stage = {.debt = 999'999'998, .cover = 99'999'998, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'999, .cover = 99'999'998, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'998, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 99'999'998, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 99'999'998, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'999, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'999, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 100'000'001, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .cover = 100'000'001, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 100'000'001, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'002, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        // debt 1'000'000'001, rate 10'000, cover 100'000'001
        {.stage = {.debt = 999'999'999, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'003, .cover = 99'999'999, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'999, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'003, .cover = 100'000'000, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'999, .cover = 100'000'001, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 100'000'001, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'003, .cover = 100'000'001, .coverRate = 10'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'999, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'002, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'003, .cover = 100'000'002, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .cover = 100'000'003, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'003, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'003, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'002, .cover = 100'000'003, .coverRate = 10'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'003, .cover = 100'000'003, .coverRate = 10'000}, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 100'000, cover 1'000'000'000
        {.stage = {.debt = 999'999'998, .cover = 999'999'998, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'999, .cover = 999'999'998, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 999'999'998, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 999'999'998, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 999'999'999, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .cover = 999'999'999, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 999'999'999, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 999'999'999, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 1'000'000'000, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .cover = 1'000'000'000, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 1'000'000'000, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 1'000'000'000, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 1'000'000'001, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .cover = 1'000'000'001, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 1'000'000'001, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'002, .cover = 1'000'000'001, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 999'999'998, .cover = 1'000'000'002, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999, .cover = 1'000'000'002, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 1'000'000'002, .coverRate = 100'000}, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'002, .cover = 1'000'000'002, .coverRate = 100'000}, .expected = tecINSUFFICIENT_FUNDS},
    };
    static constexpr LoanBrokerCoverClawbackCase kCoverClawbackClamp[] = {
        // debt 1, rate 1, cover 2, amount 1
        {.stage = {.debt = 1, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 1, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 2, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 3, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 3, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 3, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 4, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 4, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1, .cover = 4, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        // debt 100'000, rate 1, cover 2, amount 1
        {.stage = {.debt = 100'000, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 1, .coverRate = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 1, .coverRate = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 1, .coverRate = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 100'000, .cover = 2, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 2, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 2, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 3, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 3, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 3, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 4, .coverRate = 1}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 4, .coverRate = 1}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 100'000, .cover = 4, .coverRate = 1}, .amount = 3, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 10'000, cover 100'000'001, amount 1
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 99'999'999, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'000, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'001, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'002, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'003, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'003, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 100'000'003, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 10'000, cover 1'000'000'000, amount 900'000'000
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 900'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'998, .coverRate = 10'000}, .amount = 900'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 900'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 10'000}, .amount = 900'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 900'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 10'000}, .amount = 900'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 900'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 10'000}, .amount = 900'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 899'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 899'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 900'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 900'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 10'000}, .amount = 900'000'002, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 10'000, cover 200'000'000, amount 100'000'000
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 100'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'998, .coverRate = 10'000}, .amount = 100'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 100'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 199'999'999, .coverRate = 10'000}, .amount = 100'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 100'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'000, .coverRate = 10'000}, .amount = 100'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 100'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'001, .coverRate = 10'000}, .amount = 100'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 99'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 99'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 100'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 100'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 200'000'002, .coverRate = 10'000}, .amount = 100'000'002, .expected = tesSUCCESS},
        // debt 1'000'000'001, rate 10'000, cover 100'000'002, amount 1
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'000, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'001, .coverRate = 10'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'002, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'003, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'003, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'003, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'004, .coverRate = 10'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'004, .coverRate = 10'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001, .cover = 100'000'004, .coverRate = 10'000}, .amount = 3, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 1, cover 1'000'010'000, amount 1'000'000'000
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'998, .coverRate = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'009'999, .coverRate = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'000, .coverRate = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'001, .coverRate = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'010'002, .coverRate = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // debt 1'000'000'000, rate 100'000, cover 1'000'000'001, amount 1
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 100'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 100'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 999'999'999, .coverRate = 100'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 100'000}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 100'000}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'000, .coverRate = 100'000}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 100'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 100'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'001, .coverRate = 100'000}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 100'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 100'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'002, .coverRate = 100'000}, .amount = 3, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'003, .coverRate = 100'000}, .amount = 1, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'003, .coverRate = 100'000}, .amount = 2, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000, .cover = 1'000'000'003, .coverRate = 100'000}, .amount = 3, .expected = tesSUCCESS},
    };
    // clang-format on

    void
    runLoanBrokerCoverDepositBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanBrokerCoverDepositCase const> cases) {
            testcase("cover deposit " + name);
            for (TestLedger const& ledger : ledgers)
            {
                BrokerFixture const& f = ledger.f;
                for (std::size_t i = 0; auto const& [stage, amount, exponent, expected] : cases)
                    checkCover(
                        ledger,
                        stage,
                        CoverOp::Deposit,
                        units(f, amount, exponent),
                        expected,
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)));
            }
        };

        run("sub-grid", s.iou, kCoverDepositSubGrid);
        run("truncation", s.iou, kCoverDepositTruncation);
        run("open limit", s.all, kCoverDepositOpenLimit);
    }

    void
    testLoanBrokerCoverDepositBoundaries(LendingSetup const& s)
    {
        runLoanBrokerCoverDepositBoundaries(s);
    }

    void
    runLoanBrokerCoverWithdrawBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanBrokerCoverWithdrawCase const> cases) {
            testcase("cover withdraw " + name);
            for (TestLedger const& ledger : ledgers)
            {
                BrokerFixture const& f = ledger.f;
                for (std::size_t i = 0; auto const& [stage, amount, exponent, expected] : cases)
                    checkCover(
                        ledger,
                        stage,
                        CoverOp::Withdraw,
                        units(f, amount, exponent),
                        expected,
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)));
            }
        };

        run("sub-grid", s.iou, kCoverWithdrawSubGrid);
        run("whole cover", s.all, kCoverWithdrawAll);
        run("minimum cover", s.all, kCoverWithdrawMinimum);
    }

    void
    testLoanBrokerCoverWithdrawBoundaries(LendingSetup const& s)
    {
        runLoanBrokerCoverWithdrawBoundaries(s);
    }

    void
    runLoanBrokerCoverClawbackBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanBrokerCoverClawbackCase const> cases) {
            testcase("cover clawback " + name);
            for (TestLedger const& ledger : ledgers)
            {
                for (std::size_t i = 0; auto const& [stage, amount, exponent, expected] : cases)
                {
                    checkCover(
                        ledger,
                        stage,
                        CoverOp::Clawback,
                        amount ? std::optional{units(ledger.f, *amount, exponent)} : std::nullopt,
                        expected,
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)));
                }
            }
        };

        run("sub-grid", s.iou, kCoverClawbackSubGrid);
        run("no excess", s.all, kCoverClawbackNoExcess);
        run("clamp", s.all, kCoverClawbackClamp);
    }

    void
    testLoanBrokerCoverClawbackBoundaries(LendingSetup const& s)
    {
        runLoanBrokerCoverClawbackBoundaries(s);
    }

    void
    runTests() override
    {
        jtx::Env iouEnv{*this, lendingTestAmendments()};
        jtx::Env mptEnv{*this, lendingTestAmendments()};
        LendingSetup const s = setUpLending(iouEnv, mptEnv);

        // The IOU vault has scale 6, so the cover grid is 1e-6 and the open limit 9e9.
        Number const grid{1, -6};
        Number const openLimit = units(s.iouLedger.f, kOpenLimitUnits);

        struct CoverTest
        {
            char const* name;
            CoverOp op;
            Number initialCover{0};
            bool withLoan = false;
            std::optional<Number> amount{};
            TER expected;
            std::optional<Number> expectedMoved{};
            LendingAsset asset = LendingAsset::iou;
        };
        // Not static: rows use the open limit of this run's fixture.
        // clang-format off
        CoverTest const coverTests[] = {
            // Deposits
            {.name = "first deposit", .op = CoverOp::Deposit, .amount = Number{100}, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            {.name = "second deposit", .op = CoverOp::Deposit, .initialCover = Number{100}, .amount = Number{50}, .expected = tesSUCCESS, .expectedMoved = Number{50}},
            {.name = "off-grid amount is truncated", .op = CoverOp::Deposit, .initialCover = Number{100}, .amount = Number{1'234'567, -7}, .expected = tesSUCCESS, .expectedMoved = Number{123'456, -6}},
            // Covered by testLoanBrokerCoverDepositBoundaries.
            {.name = "sub-grid dust", .op = CoverOp::Deposit, .initialCover = Number{100}, .amount = Number{1, -7}, .expected = tecPRECISION_LOSS},
            {.name = "up to the open limit", .op = CoverOp::Deposit, .amount = openLimit, .expected = tesSUCCESS, .expectedMoved = openLimit},
            {.name = "17-digit cover leaves the base exponent", .op = CoverOp::Deposit, .amount = Number{1, 10}, .expected = tecLIMIT_EXCEEDED},
            // Covered by testLoanBrokerCoverDepositBoundaries.
            {.name = "past the open limit", .op = CoverOp::Deposit, .amount = openLimit + grid, .expected = tecLIMIT_EXCEEDED},

            // Withdrawals
            {.name = "partial", .op = CoverOp::Withdraw, .initialCover = Number{100}, .amount = Number{40}, .expected = tesSUCCESS, .expectedMoved = Number{40}},
            {.name = "everything", .op = CoverOp::Withdraw, .initialCover = Number{100}, .amount = Number{100}, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            // Covered by testLoanBrokerCoverWithdrawBoundaries.
            {.name = "more than available", .op = CoverOp::Withdraw, .initialCover = Number{100}, .amount = Number{101}, .expected = tecINSUFFICIENT_FUNDS},
            // Covered by testLoanBrokerCoverWithdrawBoundaries.
            {.name = "sub-grid dust", .op = CoverOp::Withdraw, .initialCover = Number{100}, .amount = Number{1, -7}, .expected = tecPRECISION_LOSS},
            {.name = "down to the minimum cover", .op = CoverOp::Withdraw, .initialCover = Number{200}, .withLoan = true, .amount = Number{100}, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            // Covered by testLoanBrokerCoverWithdrawBoundaries.
            {.name = "below the minimum cover", .op = CoverOp::Withdraw, .initialCover = Number{200}, .withLoan = true, .amount = Number{150}, .expected = tecINSUFFICIENT_FUNDS},

            // Clawbacks by the issuer
            {.name = "no amount claws everything", .op = CoverOp::Clawback, .initialCover = Number{100}, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            {.name = "zero amount claws everything", .op = CoverOp::Clawback, .initialCover = Number{100}, .amount = Number{0}, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            {.name = "partial", .op = CoverOp::Clawback, .initialCover = Number{100}, .amount = Number{40}, .expected = tesSUCCESS, .expectedMoved = Number{40}},
            {.name = "above the excess is clamped", .op = CoverOp::Clawback, .initialCover = Number{100}, .amount = Number{150}, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            {.name = "only the excess over the minimum cover", .op = CoverOp::Clawback, .initialCover = Number{200}, .withLoan = true, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            {.name = "clamped to the excess over the minimum cover", .op = CoverOp::Clawback, .initialCover = Number{200}, .withLoan = true, .amount = Number{150}, .expected = tesSUCCESS, .expectedMoved = Number{100}},
            // Covered by testLoanBrokerCoverClawbackBoundaries.
            {.name = "no excess cover", .op = CoverOp::Clawback, .expected = tecINSUFFICIENT_FUNDS},
            // Covered by testLoanBrokerCoverClawbackBoundaries.
            {.name = "sub-grid dust", .op = CoverOp::Clawback, .initialCover = Number{100}, .amount = Number{1, -7}, .expected = tecPRECISION_LOSS},

            // An MPT cover is integral: no rounding to the cover grid.
            {.name = "MPT", .op = CoverOp::Deposit, .amount = Number{100}, .expected = tesSUCCESS, .expectedMoved = Number{100}, .asset = LendingAsset::mpt},
            {.name = "MPT", .op = CoverOp::Withdraw, .initialCover = Number{100}, .amount = Number{40}, .expected = tesSUCCESS, .expectedMoved = Number{40}, .asset = LendingAsset::mpt},
            {.name = "MPT", .op = CoverOp::Clawback, .initialCover = Number{100}, .amount = Number{40}, .expected = tesSUCCESS, .expectedMoved = Number{40}, .asset = LendingAsset::mpt},
            {.name = "MPT excess over the minimum cover", .op = CoverOp::Clawback, .initialCover = Number{200}, .withLoan = true, .expected = tesSUCCESS, .expectedMoved = Number{100}, .asset = LendingAsset::mpt},
        };
        // clang-format on
        for (CoverTest const& t : coverTests)
            runCover(
                s,
                t.name,
                t.op,
                t.initialCover,
                t.withLoan,
                t.amount,
                t.expected,
                t.expectedMoved,
                t.asset);

        testLoanBrokerCoverDepositBoundaries(s);
        testLoanBrokerCoverWithdrawBoundaries(s);
        testLoanBrokerCoverClawbackBoundaries(s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanBrokerCover, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
