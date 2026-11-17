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
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>

#include <cstddef>
#include <cstdint>
#include <exception>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// A LoanBrokerSet on a broker staged as `stage` (vault grid units): a new broker of the vault or,
// with `update`, an update of the staged one. A C++ preflight rejection (tem) is paired with
// `leanError`, the model error that stands for it.
struct LoanBrokerSetCase
{
    LendingStage stage{};
    std::optional<std::int64_t> debtMaximum{};
    // DebtMaximum is debtMaximum * 10^exponent vault grid units.
    int exponent{};
    std::optional<std::uint16_t> managementFeeRate{};
    std::optional<std::uint32_t> coverRateMinimum{};
    std::optional<std::uint32_t> coverRateLiquidation{};
    bool update{};
    TER expected;
    std::optional<LeanError> leanError{};
};

// Differential tests of the loan broker's lawful state and of LoanBrokerSet (create and update)
// and LoanBrokerDelete against the model.
// Rows stage ledger state on a throwaway view, including states no transaction sequence may
// reach: a verdict compares model and C++ on the same pre-state, not a claim the state is
// reachable (see stageLending).
class LeanLoanBroker_test : public LeanSuite
{
    // A valid broker: IOU asset, 1% management fee, 10% / 20% cover rates, some cover, no loans.
    static LoanBroker
    baseline()
    {
        return {
            .numericType = 2,
            .managementFeeRate = 1'000,
            .coverRateMinimum = 10'000,
            .coverRateLiquidation = 20'000,
            .debtTotal = Number{0},
            .debtMaximum = Number{0},
            .coverAvailable = Number{100},
            .loanCount = 0};
    }

    using Mutation = std::function<void(LoanBroker&)>;

    // `mutate` applied to the baseline: build accepts the broker or rejects it.
    void
    expectValid(std::string const& label, Mutation const& mutate = {})
    {
        expectBuild(label, mutate, true);
    }

    void
    expectInvalid(std::string const& label, Mutation const& mutate)
    {
        expectBuild(label, mutate, false);
    }

    void
    expectBuild(std::string const& label, Mutation const& mutate, bool valid)
    {
        LoanBroker broker = baseline();
        if (mutate)
            mutate(broker);
        testcase(label);
        BEAST_EXPECTS(LoanBrokerFFI::build(broker).has_value() == valid, label);
    }

    void
    testLawful()
    {
        expectValid("valid baseline");
        expectValid("broker with a loan under its cap", [](LoanBroker& broker) {
            broker.loanCount = 1;
            broker.debtTotal = Number{500};
            broker.debtMaximum = Number{1'000};
        });
        expectValid("broker without cover rates", [](LoanBroker& broker) {
            broker.coverRateMinimum = 0;
            broker.coverRateLiquidation = 0;
        });
        expectInvalid(
            "negative debtTotal", [](LoanBroker& broker) { broker.debtTotal = Number{-1}; });
        expectInvalid("negative coverAvailable", [](LoanBroker& broker) {
            broker.coverAvailable = Number{-1};
        });
        expectInvalid("debtTotal above debtMaximum", [](LoanBroker& broker) {
            broker.loanCount = 1;
            broker.debtTotal = Number{500};
            broker.debtMaximum = Number{100};
        });
        expectInvalid(
            "debt without a loan", [](LoanBroker& broker) { broker.debtTotal = Number{500}; });
        expectInvalid(
            "negative debtMaximum", [](LoanBroker& broker) { broker.debtMaximum = Number{-1}; });
        expectInvalid("debtMaximum above 2^63-1", [](LoanBroker& broker) {
            broker.debtMaximum = Number{1, 19};
        });
        expectInvalid("management fee above 10%", [](LoanBroker& broker) {
            broker.managementFeeRate = 10'001;
        });
        expectInvalid("minimum cover rate above 100%", [](LoanBroker& broker) {
            broker.coverRateMinimum = 100'001;
        });
        expectInvalid("liquidation cover rate above 100%", [](LoanBroker& broker) {
            broker.coverRateLiquidation = 100'001;
        });
        expectInvalid("minimum cover rate without a liquidation rate", [](LoanBroker& broker) {
            broker.coverRateLiquidation = 0;
        });
        expectInvalid("liquidation cover rate without a minimum rate", [](LoanBroker& broker) {
            broker.coverRateMinimum = 0;
        });
    }

    // LoanBrokerSet on `view` and the model on the same pre-state. A C++ preflight rejection (tem)
    // is paired with `leanError`, the model error that stands for it.
    AppliedBrokerTx
    checkLoanBrokerSet(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        LoanBrokerSetArgs const& args,
        bool update,
        TER expected,
        std::optional<LeanError> leanError,
        std::string const& at)
    {
        AppliedBrokerTx const cpp = applyLoanBrokerSet(env, view, f, args, update);
        LeanBrokerTx const lean = leanLoanBrokerSet(cpp, args, update);
        expectRow(*this, at, cpp, lean, expected, leanError);
        return cpp;
    }

    static std::string
    setText(LendingStage const& stage, LoanBrokerSetArgs const& args, bool update)
    {
        auto const opt = [](auto const& o) { return o ? std::to_string(*o) : std::string{"none"}; };
        return std::string{update ? "update" : "create"} + " debt maximum " +
            (args.debtMaximum ? to_string(*args.debtMaximum) : std::string{"none"}) + ", fee " +
            opt(args.managementFeeRate) + ", rates " + opt(args.coverRateMinimum) + "/" +
            opt(args.coverRateLiquidation) + ", " + stageText(stage) + ": ";
    }

    // Model of LoanBrokerSet creating a broker, on the shared IOU ledger (a second broker of its
    // vault); `openEnded` needs its own ledger, without a broker.
    void
    runCreate(
        LendingSetup const& s,
        std::string const& label,
        BrokerConfig const& config,
        bool openEnded,
        TER expected,
        std::optional<LeanError> leanError = std::nullopt)
    {
        using namespace jtx;
        testcase(label);
        LoanBrokerSetArgs const args{
            .debtMaximum = config.debtMaximum,
            .managementFeeRate = config.managementFeeRate,
            .coverRateMinimum = config.coverRateMinimum,
            .coverRateLiquidation = config.coverRateLiquidation,
        };
        if (openEnded)
        {
            Env env{*this, lendingTestAmendments()};
            auto const f = setUpBrokerVault(env, std::nullopt, Number{10'000}, openEnded, false);
            OpenView view{*env.current()};
            checkLoanBrokerSet(env, f, view, args, false, expected, leanError, label + ": ");
            return;
        }
        TestLedger const& l = s.iouLedger;
        OpenView view{*l.env->current()};
        stageInvestment(*l.env, view, l.f, {});
        checkLoanBrokerSet(*l.env, l.f, view, args, false, expected, leanError, label + ": ");
    }

    // Model of LoanBrokerSet updating the debt maximum, staged on the shared IOU ledger: a broker
    // with a debt maximum of 5000 and, with `withLoan`, a loan of 1000 (so its debt is non-zero).
    void
    runUpdate(
        LendingSetup const& s,
        std::string const& label,
        std::optional<Number> const& debtMaximum,
        bool withLoan,
        TER expected,
        bool equalToDebt = false)
    {
        testcase(label);
        TestLedger const& l = s.iouLedger;
        OpenView view{*l.env->current()};
        LendingStage stage{
            .managementFeeRate = 1'000,
            .coverRate = 10'000,
            .debtMaximum = 5'000'000'000,
        };
        if (withLoan)
        {
            stage.debt = 1'000'000'000;
            stage.cover = 200'000'000;
        }
        stageInvestment(*l.env, view, l.f, stage);
        LoanBrokerSetArgs const args{
            .debtMaximum =
                equalToDebt ? std::optional<Number>{readBroker(view, l.f).debtTotal} : debtMaximum,
        };
        checkLoanBrokerSet(*l.env, l.f, view, args, true, expected, std::nullopt, label + ": ");
    }

    // Each row stages the asset's shared ledger on a throwaway view (the vault in its investment
    // phase), applies LoanBrokerSet there and expects its verdict on both sides, with every field
    // of the broker equal when both succeed. Debt maximum rows are in units of the vault grid.
    // A group comment names a boundary value (the cusp); its rows step those values around it.
    // - Debt maximum grid: a debt maximum off the vault grid is tecPRECISION_LOSS, on create and on
    //   update. Each cusp is one step of 10^level units with a 16-digit mantissa; moving the
    //   mantissa leaves the grid.
    // - Debt maximum digits (IOU): a debt maximum a 16-digit mantissa cannot hold is
    //   tecPRECISION_LOSS: 1e16 units is exact, one unit more is not.
    // - Debt maximum cap: above 2^63 - 1 is temINVALID (the model: not lawful). The cusp is the
    //   largest 16-digit mantissa at exponent 3 under the cap.
    // - Debt maximum update: lowering the debt maximum below the broker's debt is
    //   tecLIMIT_EXCEEDED (zero means no maximum). Each cusp sets it to exactly the debt.
    // - Debt maximum zero: a negative debt maximum is temINVALID (not lawful); zero means no
    //   maximum. On create and on update.
    // - Rate caps (IOU): a management fee above 10% or a cover rate above 100% is temINVALID (not
    //   lawful). The cover rates move one at a time with the other at the cap.
    // Fixed fields on update (management fee, cover rates: temINVALID) are a preflight check
    // outside the model, whose update takes only the debt maximum.
    // clang-format off
    static constexpr LoanBrokerSetCase kDebtMaximumGrid[] = {
        // one step of 1e0 units
        {.debtMaximum = 999'999'999'999'998, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 999'999'999'999'999, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'000, .exponent = -15, .expected = tesSUCCESS},
        {.debtMaximum = 1'000'000'000'000'001, .exponent = -15, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'002, .exponent = -15, .expected = tecPRECISION_LOSS},
        // one step of 1e9 units
        {.debtMaximum = 999'999'999'999'998, .exponent = -6, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 999'999'999'999'999, .exponent = -6, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'000, .exponent = -6, .expected = tesSUCCESS},
        {.debtMaximum = 1'000'000'000'000'001, .exponent = -6, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'002, .exponent = -6, .expected = tecPRECISION_LOSS},
        // one step of 1e14 units
        {.debtMaximum = 999'999'999'999'998, .exponent = -1, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 999'999'999'999'999, .exponent = -1, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'000, .exponent = -1, .expected = tesSUCCESS},
        {.debtMaximum = 1'000'000'000'000'001, .exponent = -1, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'002, .exponent = -1, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanBrokerSetCase kDebtMaximumUpdateGrid[] = {
        // one step of 1e0 units
        {.debtMaximum = 999'999'999'999'998, .exponent = -15, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 999'999'999'999'999, .exponent = -15, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'000, .exponent = -15, .update = true, .expected = tesSUCCESS},
        {.debtMaximum = 1'000'000'000'000'001, .exponent = -15, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'002, .exponent = -15, .update = true, .expected = tecPRECISION_LOSS},
        // one step of 1e9 units
        {.debtMaximum = 999'999'999'999'998, .exponent = -6, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 999'999'999'999'999, .exponent = -6, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'000, .exponent = -6, .update = true, .expected = tesSUCCESS},
        {.debtMaximum = 1'000'000'000'000'001, .exponent = -6, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'002, .exponent = -6, .update = true, .expected = tecPRECISION_LOSS},
        // one step of 1e14 units
        {.debtMaximum = 999'999'999'999'998, .exponent = -1, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 999'999'999'999'999, .exponent = -1, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'000, .exponent = -1, .update = true, .expected = tesSUCCESS},
        {.debtMaximum = 1'000'000'000'000'001, .exponent = -1, .update = true, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 1'000'000'000'000'002, .exponent = -1, .update = true, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanBrokerSetCase kDebtMaximumDigits[] = {
        // 1e16 units
        {.debtMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.debtMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.debtMaximum = 10'000'000'000'000'000, .expected = tesSUCCESS},
        {.debtMaximum = 10'000'000'000'000'001, .expected = tecPRECISION_LOSS},
        {.debtMaximum = 10'000'000'000'000'002, .expected = tecPRECISION_LOSS},
    };
    static constexpr LoanBrokerSetCase kDebtMaximumCapIou[] = {
        // 2^63 - 1 at exponent 3
        {.debtMaximum = 9'223'372'036'854'773, .exponent = 9, .expected = tesSUCCESS},
        {.debtMaximum = 9'223'372'036'854'774, .exponent = 9, .expected = tesSUCCESS},
        {.debtMaximum = 9'223'372'036'854'775, .exponent = 9, .expected = tesSUCCESS},
        {.debtMaximum = 9'223'372'036'854'776, .exponent = 9, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.debtMaximum = 9'223'372'036'854'777, .exponent = 9, .expected = temINVALID, .leanError = LeanError::notLawful},
    };
    static constexpr LoanBrokerSetCase kDebtMaximumCapMpt[] = {
        // 2^63 - 1 at exponent 3
        {.debtMaximum = 9'223'372'036'854'773, .exponent = 3, .expected = tesSUCCESS},
        {.debtMaximum = 9'223'372'036'854'774, .exponent = 3, .expected = tesSUCCESS},
        {.debtMaximum = 9'223'372'036'854'775, .exponent = 3, .expected = tesSUCCESS},
        {.debtMaximum = 9'223'372'036'854'776, .exponent = 3, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.debtMaximum = 9'223'372'036'854'777, .exponent = 3, .expected = temINVALID, .leanError = LeanError::notLawful},
    };
    static constexpr LoanBrokerSetCase kDebtMaximumUpdate[] = {
        // debt 1, maximum 1
        {.stage = {}, .debtMaximum = 0, .update = true, .expected = tesSUCCESS},
        {.stage = {}, .debtMaximum = 1, .update = true, .expected = tesSUCCESS},
        {.stage = {}, .debtMaximum = 2, .update = true, .expected = tesSUCCESS},
        {.stage = {}, .debtMaximum = 3, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1}, .debtMaximum = 0, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1}, .debtMaximum = 1, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1}, .debtMaximum = 2, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1}, .debtMaximum = 3, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 2}, .debtMaximum = 0, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 2}, .debtMaximum = 1, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 2}, .debtMaximum = 2, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 2}, .debtMaximum = 3, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 3}, .debtMaximum = 0, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 3}, .debtMaximum = 1, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3}, .debtMaximum = 2, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 3}, .debtMaximum = 3, .update = true, .expected = tesSUCCESS},
        // debt 1'000'000'000, maximum 1'000'000'000
        {.stage = {.debt = 999'999'998}, .debtMaximum = 999'999'998, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998}, .debtMaximum = 999'999'999, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998}, .debtMaximum = 1'000'000'000, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998}, .debtMaximum = 1'000'000'001, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'998}, .debtMaximum = 1'000'000'002, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999}, .debtMaximum = 999'999'998, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 999'999'999}, .debtMaximum = 999'999'999, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999}, .debtMaximum = 1'000'000'000, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999}, .debtMaximum = 1'000'000'001, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 999'999'999}, .debtMaximum = 1'000'000'002, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000}, .debtMaximum = 999'999'998, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000}, .debtMaximum = 999'999'999, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'000}, .debtMaximum = 1'000'000'000, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000}, .debtMaximum = 1'000'000'001, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'000}, .debtMaximum = 1'000'000'002, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001}, .debtMaximum = 999'999'998, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'001}, .debtMaximum = 999'999'999, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'001}, .debtMaximum = 1'000'000'000, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'001}, .debtMaximum = 1'000'000'001, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'001}, .debtMaximum = 1'000'000'002, .update = true, .expected = tesSUCCESS},
        {.stage = {.debt = 1'000'000'002}, .debtMaximum = 999'999'998, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'002}, .debtMaximum = 999'999'999, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'002}, .debtMaximum = 1'000'000'000, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'002}, .debtMaximum = 1'000'000'001, .update = true, .expected = tecLIMIT_EXCEEDED},
        {.stage = {.debt = 1'000'000'002}, .debtMaximum = 1'000'000'002, .update = true, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerSetCase kDebtMaximumZero[] = {
        // zero
        {.debtMaximum = -2, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.debtMaximum = -1, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.debtMaximum = 0, .expected = tesSUCCESS},
        {.debtMaximum = 1, .expected = tesSUCCESS},
        {.debtMaximum = 2, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerSetCase kDebtMaximumUpdateZero[] = {
        // zero
        {.debtMaximum = -2, .update = true, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.debtMaximum = -1, .update = true, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.debtMaximum = 0, .update = true, .expected = tesSUCCESS},
        {.debtMaximum = 1, .update = true, .expected = tesSUCCESS},
        {.debtMaximum = 2, .update = true, .expected = tesSUCCESS},
    };
    static constexpr LoanBrokerSetCase kManagementFeeCap[] = {
        // 10%
        {.managementFeeRate = 9'998, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'000, .expected = tesSUCCESS},
        {.managementFeeRate = 9'999, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'000, .expected = tesSUCCESS},
        {.managementFeeRate = 10'000, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'000, .expected = tesSUCCESS},
        {.managementFeeRate = 10'001, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'000, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.managementFeeRate = 10'002, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'000, .expected = temINVALID, .leanError = LeanError::notLawful},
    };
    static constexpr LoanBrokerSetCase kMinimumCoverRateCap[] = {
        // 100%
        {.managementFeeRate = 0, .coverRateMinimum = 99'998, .coverRateLiquidation = 100'000, .expected = tesSUCCESS},
        {.managementFeeRate = 0, .coverRateMinimum = 99'999, .coverRateLiquidation = 100'000, .expected = tesSUCCESS},
        {.managementFeeRate = 0, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'000, .expected = tesSUCCESS},
        {.managementFeeRate = 0, .coverRateMinimum = 100'001, .coverRateLiquidation = 100'000, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.managementFeeRate = 0, .coverRateMinimum = 100'002, .coverRateLiquidation = 100'000, .expected = temINVALID, .leanError = LeanError::notLawful},
    };
    static constexpr LoanBrokerSetCase kLiquidationCoverRateCap[] = {
        // 100%
        {.managementFeeRate = 0, .coverRateMinimum = 100'000, .coverRateLiquidation = 99'998, .expected = tesSUCCESS},
        {.managementFeeRate = 0, .coverRateMinimum = 100'000, .coverRateLiquidation = 99'999, .expected = tesSUCCESS},
        {.managementFeeRate = 0, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'000, .expected = tesSUCCESS},
        {.managementFeeRate = 0, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'001, .expected = temINVALID, .leanError = LeanError::notLawful},
        {.managementFeeRate = 0, .coverRateMinimum = 100'000, .coverRateLiquidation = 100'002, .expected = temINVALID, .leanError = LeanError::notLawful},
    };
    // clang-format on

    void
    runLoanBrokerSetBoundaries(LendingSetup const& s)
    {
        auto const run = [&](std::string const& name,
                             std::vector<TestLedger> const& ledgers,
                             std::span<LoanBrokerSetCase const> cases) {
            testcase("LoanBrokerSet " + name);
            for (TestLedger const& ledger : ledgers)
            {
                for (std::size_t i = 0; LoanBrokerSetCase const& c : cases)
                {
                    LoanBrokerSetArgs const args{
                        .debtMaximum = c.debtMaximum
                            ? std::optional{units(ledger.f, *c.debtMaximum, c.exponent)}
                            : std::nullopt,
                        .managementFeeRate = c.managementFeeRate,
                        .coverRateMinimum = c.coverRateMinimum,
                        .coverRateLiquidation = c.coverRateLiquidation,
                    };
                    OpenView view{*ledger.env->current()};
                    stageInvestment(*ledger.env, view, ledger.f, c.stage);
                    checkLoanBrokerSet(
                        *ledger.env,
                        ledger.f,
                        view,
                        args,
                        c.update,
                        c.expected,
                        c.leanError,
                        rowText(i++, vaultName(*ledger.env, ledger.f.vaultKeylet)) +
                            setText(c.stage, args, c.update));
                }
            }
        };

        run("debt maximum grid", s.all, kDebtMaximumGrid);
        run("debt maximum update grid", s.all, kDebtMaximumUpdateGrid);
        run("debt maximum digits", s.iou, kDebtMaximumDigits);
        run("debt maximum cap", s.iou, kDebtMaximumCapIou);
        run("debt maximum cap", s.mpt, kDebtMaximumCapMpt);
        run("debt maximum update", s.all, kDebtMaximumUpdate);
        run("debt maximum zero", s.all, kDebtMaximumZero);
        run("debt maximum update zero", s.all, kDebtMaximumUpdateZero);
        run("management fee cap", s.iou, kManagementFeeCap);
        run("minimum cover rate cap", s.iou, kMinimumCoverRateCap);
        run("liquidation cover rate cap", s.iou, kLiquidationCoverRateCap);
    }

    void
    testLoanBrokerSetBoundaries(LendingSetup const& s)
    {
        runLoanBrokerSetBoundaries(s);
    }

    // Model of LoanBrokerDelete: canDelete is preclaim; the cover returned to the owner is the
    // broker's rounded coverAvailable.
    void
    runDelete(std::string const& label, Number const& cover, bool withLoan, TER expected)
    {
        using namespace jtx;
        testcase(label);

        Env env{*this, lendingTestAmendments()};
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        if (cover != Number{0})
            depositCover(env, f, cover);
        if (withLoan)
            issueLoan(env, f, Number{1'000});

        LoanBroker const broker = readBroker(*env.current(), f.brokerKeylet, f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LawfulTerResult const canDelete = leanCanLoanBrokerDelete(broker, pool);
        expectLawful(canDelete);
        LeanRoundedCoverResult const rounded = leanLoanBrokerRoundedCover(broker);

        Number const ownerBefore = iouBalance(env, f.owner, f.asset);
        env(loan_broker::del(f.owner, f.brokerKeylet.key), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!canDelete.leanError.has_value(), "lean canDelete error");
        BEAST_EXPECTS(
            canDelete.ter == cppTer,
            std::string("lean=") + transToken(canDelete.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return;
        BEAST_EXPECT(!env.le(f.brokerKeylet));
        BEAST_EXPECTS(!rounded.leanError.has_value(), "lean roundedCoverAvailable error");
        Number const received = iouBalance(env, f.owner, f.asset) - ownerBefore;
        BEAST_EXPECTS(
            Number{rounded.amount} == received,
            "cover returned lean=" + to_string(Number{rounded.amount}) +
                " cpp=" + to_string(received));
    }

    void
    runTests() override
    {
        jtx::Env iouEnv{*this, lendingTestAmendments()};
        jtx::Env mptEnv{*this, lendingTestAmendments()};
        LendingSetup const s = setUpLending(iouEnv, mptEnv);

        testLawful();

        // LoanBrokerSet: create
        struct CreateRow
        {
            char const* label;
            BrokerConfig config{};
            bool openEnded = false;
            TER expected;
            std::optional<LeanError> leanError{};
        };
        // clang-format off
        static CreateRow const kCreateRows[] = {
            {.label = "create a broker on a closed-ended vault", .expected = tesSUCCESS},
            {.label = "create a broker with a debt maximum", .config = {.debtMaximum = Number{1'000'000}}, .expected = tesSUCCESS},
            {.label = "create a broker without cover rates", .config = {.coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt}, .expected = tesSUCCESS},
            {.label = "create a broker on an open-ended vault", .openEnded = true, .expected = tecNO_PERMISSION},
            {.label = "create a broker with a debt maximum off the vault grid", .config = {.debtMaximum = Number{1, -7}}, .expected = tecPRECISION_LOSS},
            {.label = "create a broker with a debt maximum not representable as an amount", .config = {.debtMaximum = Number{12'345'678'901'234'567LL, -10}}, .expected = tecPRECISION_LOSS},
            {.label = "create a broker with a negative debt maximum", .config = {.debtMaximum = Number{-1}}, .expected = temINVALID, .leanError = LeanError::notLawful},
            {.label = "create a broker with a management fee above 10%", .config = {.managementFeeRate = 10'001}, .expected = temINVALID, .leanError = LeanError::notLawful},
            {.label = "create a broker with a cover rate above 100%", .config = {.coverRateMinimum = 100'001}, .expected = temINVALID, .leanError = LeanError::notLawful},
            {.label = "create a broker with a minimum cover rate but no liquidation rate", .config = {.coverRateLiquidation = std::nullopt}, .expected = temINVALID, .leanError = LeanError::notLawful},
        };
        // clang-format on
        for (CreateRow const& r : kCreateRows)
            runCreate(s, r.label, r.config, r.openEnded, r.expected, r.leanError);

        // LoanBrokerSet: update a broker with a debt maximum of 5000 and, `withLoan`, a debt of
        // 1000.
        struct UpdateRow
        {
            char const* label;
            std::optional<Number> debtMaximum{};
            bool withLoan = false;
            TER expected;
            bool equalToDebt = false;
        };
        // clang-format off
        static UpdateRow const kUpdateRows[] = {
            {.label = "raise the debt maximum", .debtMaximum = Number{8'000}, .expected = tesSUCCESS},
            {.label = "lift the debt maximum", .debtMaximum = Number{0}, .expected = tesSUCCESS},
            {.label = "update without a debt maximum", .expected = tesSUCCESS},
            {.label = "debt maximum off the vault grid", .debtMaximum = Number{1, -7}, .expected = tecPRECISION_LOSS},
            {.label = "debt maximum not representable as an amount", .debtMaximum = Number{12'345'678'901'234'567LL, -10}, .expected = tecPRECISION_LOSS},
            // Covered by testLoanBrokerSetBoundaries.
            {.label = "debt maximum below the debt", .debtMaximum = Number{500}, .withLoan = true, .expected = tecLIMIT_EXCEEDED},
            {.label = "debt maximum equal to the debt", .withLoan = true, .expected = tesSUCCESS, .equalToDebt = true},
        };
        // clang-format on
        for (UpdateRow const& r : kUpdateRows)
            runUpdate(s, r.label, r.debtMaximum, r.withLoan, r.expected, r.equalToDebt);

        // LoanBrokerDelete
        runDelete("delete an empty broker", Number{0}, false, tesSUCCESS);
        runDelete("delete a broker with cover", Number{123'456'789, -6}, false, tesSUCCESS);
        runDelete("delete a broker with a loan", Number{200}, true, tecHAS_OBLIGATIONS);

        testLoanBrokerSetBoundaries(s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanBroker, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
