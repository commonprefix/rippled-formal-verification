#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultDeleteFFI.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultSetFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/tx/vault/ClosedEndedSweepCases.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

// Differential tests of the vault lifecycle: every VaultDeposit and VaultWithdraw branch that
// depends on the vault phase (Subscription, Investment, Redemption) or on the early-exit fee, with
// the open-ended vault (no phase) as the reference row of each matrix. Clawback, set and delete
// have no phase logic; one closed-ended case each checks that both sides agree on that.
class LeanVaultClosedEnded_test : public LeanSuite
{
    // `onDate` puts the parent close time exactly on the date bounding the phase: the subscription
    // date is the last instant of Subscription, the redemption date the first of Redemption.
    static constexpr bool kOnDate = true;

    static std::string
    phaseName(VaultPhase phase, bool onDate)
    {
        switch (phase)
        {
            case VaultPhase::NoPhase:
                return "open-ended";
            case VaultPhase::Subscription:
                return onDate ? "at the subscription date" : "subscription";
            case VaultPhase::Investment:
                return "investment";
            case VaultPhase::Redemption:
                return onDate ? "at the redemption date" : "redemption";
        }
        return "?";
    }

    static std::string
    feeName(std::optional<std::uint32_t> earlyExitFeeRate)
    {
        if (!earlyExitFeeRate)
            return "no fee field";
        return "fee " + std::to_string(*earlyExitFeeRate) + " tenth-bips";
    }

    // Long enough for the creation and initial-deposit ledgers (5 s each) to stay in Subscription.
    static constexpr auto kSubscriptionOffset = std::chrono::seconds{600};
    static constexpr auto kInvestmentWindow = std::chrono::seconds{1'000'000};

    // Early-exit fee rates in tenth-bips.
    static constexpr std::uint32_t kFee5Pct = 5'000;
    static constexpr std::uint32_t kFee50Pct = 50'000;
    static constexpr std::uint32_t kFee100Pct = 100'000;

    struct Fixture
    {
        jtx::Account owner;
        jtx::Account issuer;
        jtx::Account holder;
        jtx::PrettyAsset asset;
        Keylet vaultKeylet;
    };

    // Land the next transaction's parent close time exactly on a schedule date.
    void
    closeOn(jtx::Env& env, NetClock::time_point at)
    {
        BEAST_EXPECTS(closeExactlyAt(env, at), "the parent close time missed the schedule date");
    }

    // Fund the accounts, create the vault (closed-ended unless `phase` is NoPhase, with the given
    // early-exit fee rate), let the holder make the initial deposit during Subscription, then
    // advance into `phase`. The schedule dates are multiples of the close-time resolution, so the
    // dates can be reached exactly.
    Fixture
    setUp(
        jtx::Env& env,
        VaultPhase phase,
        std::optional<std::uint32_t> earlyExitFeeRate,
        Number const& initialDeposit,
        bool xrp = false,
        bool onDate = false)
    {
        using namespace jtx;
        using namespace std::chrono_literals;
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        PrettyAsset const asset = xrp ? PrettyAsset{xrpIssue(), 1'000'000} : issuer["USD"];
        if (!xrp)
        {
            // Clawback must be enabled while the issuer has no trust line yet.
            env(fset(issuer, asfAllowTrustLineClawback));
            env.close();
            env(trust(owner, asset(Number{1, 10})));
            env(trust(holder, asset(Number{1, 10})));
            env.close();
            env(pay(issuer, owner, asset(10'000)));
            env(pay(issuer, holder, asset(Number{1, 10})));
            env.close();
        }

        NetClock::time_point const subscriptionDate =
            alignedTime(env, env.now() + kSubscriptionOffset);
        NetClock::time_point const redemptionDate =
            alignedTime(env, subscriptionDate + kInvestmentWindow);

        jtx::Vault vault{env};
        jtx::Vault::CreateArgs createArgs{.owner = owner, .asset = asset.raw()};
        if (phase != VaultPhase::NoPhase)
        {
            createArgs.vaultKind = std::to_underlying(VaultKind::ClosedEnded);
            createArgs.subscriptionDate = timeCount(subscriptionDate);
            createArgs.redemptionDate = timeCount(redemptionDate);
            createArgs.earlyExitFeeRate = earlyExitFeeRate;
        }
        auto const [createTx, vaultKeylet] = vault.create(createArgs);
        env(createTx);
        env.close();

        if (initialDeposit != Number{0})
        {
            env(jtx::Vault::deposit(
                    {.depositor = holder, .id = vaultKeylet.key, .amount = asset(initialDeposit)}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }

        switch (phase)
        {
            case VaultPhase::Subscription:
                if (onDate)
                    closeOn(env, subscriptionDate);
                break;
            case VaultPhase::Investment:
                env.close(subscriptionDate + 1s);
                break;
            case VaultPhase::Redemption:
                if (onDate)
                    closeOn(env, redemptionDate);
                else
                    env.close(redemptionDate + 1s);
                break;
            default:
                break;
        }
        BEAST_EXPECTS(
            getVaultPhase(*env.current(), env.le(vaultKeylet)) == phase,
            "the vault is not in the " + phaseName(phase, onDate) + " phase");
        return {owner, issuer, holder, asset, vaultKeylet};
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

    // ---- Staged samples ------------------------------------------------------------------------

    // The vaults a sweep runs on, each with the account that deposits into and withdraws from it.
    using SweepVaults = std::vector<std::pair<Keylet, jtx::Account>>;

    // 1000 IOU at scale 6, or 1000 XRP in drops: the old tests' initial deposit, in grid units and
    // in shares (price 1).
    static constexpr std::int64_t kInitialDepositUnits = 1'000'000'000;

    // The schedule dates that put the parent close time P in `phase` (on the bounding date when
    // `onDate`), the staged counterpart of setUp's ledger closes.
    static void
    stagePhase(
        StagedVault& s,
        std::uint32_t p,
        VaultPhase phase,
        std::optional<std::uint32_t> earlyExitFeeRate,
        bool onDate = false)
    {
        auto const offset = static_cast<std::uint32_t>(kSubscriptionOffset.count());
        auto const window = static_cast<std::uint32_t>(kInvestmentWindow.count());
        switch (phase)
        {
            case VaultPhase::NoPhase:
                return;
            case VaultPhase::Subscription:
                s.subscriptionDate = onDate ? p : p + offset;
                break;
            case VaultPhase::Investment:
                s.subscriptionDate = p - 1;
                break;
            case VaultPhase::Redemption:
                s.subscriptionDate = (onDate ? p : p - 1) - window;
                break;
        }
        s.redemptionDate = *s.subscriptionDate + window;
        s.earlyExitFeeRate = earlyExitFeeRate;
    }

    // A vault at price 1 holding `units` grid units, every share owned by the holder.
    static StagedVault
    depositedVault(jtx::Env& env, Keylet const& vault, std::int64_t units)
    {
        return {
            .available = gridUnits(env, vault, units),
            .sharesTotal = static_cast<std::uint64_t>(units),
            .holderShares = static_cast<std::uint64_t>(units),
            .pseudoHolding = true};
    }

    static STAmount
    shareAmount(jtx::Env& env, Keylet const& vault, std::int64_t shares)
    {
        return STAmount{MPTIssue{env.le(vault)->at(sfShareMPTID)}, shares};
    }

    void
    expectVerdict(TER cpp, TER expected)
    {
        BEAST_EXPECTS(
            cpp == expected,
            std::string("cpp=") + transToken(cpp) + " expected " + transToken(expected));
    }

    // A deposit (or donation) on a throwaway view of `staged`, and the model on the same state.
    TER
    checkDeposit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        StagedVault const& staged,
        STAmount const& amount,
        bool donate = false)
    {
        jtx::Vault::DepositArgs args{.depositor = depositor, .id = vault.key, .amount = amount};
        if (donate)
            args.flags = tfVaultDonate;
        AppliedVaultTx const cpp =
            applyStaged(env, vault, depositor, staged, jtx::Vault::deposit(args));
        LeanVaultResult const lean =
            leanVaultDeposit(cpp.pre, amount, donate, parentCloseTime(env));
        return expectAgree(*this, sampleText(staged, amount), cpp, lean);
    }

    // ---- Phase and fee matrix (staged on the shared ledger) ------------------------------------

    // Deposit matrix: a plain deposit is rejected once the vault is past Subscription, a donation
    // never is. Covered at the subscription date by testDepositSubscriptionSweep.
    void
    testDeposit(
        jtx::Env& env,
        Fixture const& f,
        VaultPhase phase,
        bool isDonation,
        TER expected,
        bool onDate = false)
    {
        testcase((isDonation ? "donate " : "deposit ") + phaseName(phase, onDate));
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), phase, std::nullopt, onDate);
        // The donor (the owner) holds no shares.
        if (isDonation)
            staged.holderShares.reset();
        expectVerdict(
            checkDeposit(
                env,
                f.vaultKeylet,
                isDonation ? f.owner : f.holder,
                staged,
                f.asset(100),
                isDonation),
            expected);
    }

    // Withdraw matrix: a withdrawal by assets of 400 from a 1000 initial deposit. Only the
    // Investment phase of a vault with an early-exit fee rate (even zero) charges the fee or,
    // without the field, rejects the withdrawal. Covered at the dates by the withdraw phase sweeps.
    void
    testWithdraw(
        jtx::Env& env,
        Fixture const& f,
        VaultPhase phase,
        std::optional<std::uint32_t> earlyExitFeeRate,
        TER expected,
        std::optional<Number> const& expectedPayout = std::nullopt,
        bool onDate = false)
    {
        testcase("withdraw " + phaseName(phase, onDate) + ", " + feeName(earlyExitFeeRate));
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), phase, earlyExitFeeRate, onDate);
        expectVerdict(
            checkWithdraw(*this, env, f.vaultKeylet, f.holder, staged, f.asset(400), expectedPayout)
                .ter,
            expected);
    }

    // By shares: 400 of the 1000 shares (scale 6: 4e8) at a 5% fee pay 380.
    void
    testWithdrawBySharesInInvestment(jtx::Env& env, Fixture const& f)
    {
        testcase("withdraw by shares in investment at a 5% fee");
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee5Pct);
        expectVerdict(
            checkWithdraw(
                *this,
                env,
                f.vaultKeylet,
                f.holder,
                staged,
                shareAmount(env, f.vaultKeylet, 400'000'000),
                Number{380})
                .ter,
            tesSUCCESS);
    }

    // A final withdrawal (all outstanding shares) skips the fee even during Investment.
    void
    testWithdrawAllSharesInInvestment(jtx::Env& env, Fixture const& f)
    {
        testcase("withdraw all shares in investment with a fee");
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee5Pct);
        expectVerdict(
            checkWithdraw(
                *this,
                env,
                f.vaultKeylet,
                f.holder,
                staged,
                shareAmount(env, f.vaultKeylet, kInitialDepositUnits),
                Number{1'000})
                .ter,
            tesSUCCESS);
    }

    // Availability is checked against the gross amount without a fee and against the net payout
    // with one: 610 of the 1000 are deployed, so withdrawing 400 fails at a zero rate and pays 380
    // at 5%.
    void
    testWithdrawGrossOverAvailable(
        jtx::Env& env,
        Fixture const& f,
        std::uint32_t earlyExitFeeRate,
        TER expected,
        Number const& available = Number{390})
    {
        testcase(
            "withdraw 400 with " + to_string(available) + " available at " +
            feeName(earlyExitFeeRate));
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        staged.available = f.asset(available);
        staged.deployed = f.asset(Number{1'000} - available);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, earlyExitFeeRate);
        expectVerdict(
            checkWithdraw(
                *this,
                env,
                f.vaultKeylet,
                f.holder,
                staged,
                f.asset(400),
                expected == tesSUCCESS ? std::optional<Number>{Number{380}} : std::nullopt)
                .ter,
            expected);
    }

    // A 16-digit amount at a 3.333% rate: the fee needs more digits than Number keeps, so the
    // upward fee and downward subtraction must round the same way on both sides.
    void
    testWithdrawInexactFee(jtx::Env& env, Fixture const& f)
    {
        testcase("withdraw a 16-digit amount at an inexact fee rate");
        // An initial deposit of 2e9 at scale 6.
        StagedVault staged = depositedVault(env, f.vaultKeylet, 2'000'000'000'000'000);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, 3'333);
        expectVerdict(
            checkWithdraw(
                *this,
                env,
                f.vaultKeylet,
                f.holder,
                staged,
                f.asset(Number{1'234'567'891'234'567LL, -6}))
                .ter,
            tesSUCCESS);
    }

    // XRP: a 50% fee on one drop leaves half a drop, which is zero in drops.
    void
    testWithdrawFeeConsumesPayout(jtx::Env& env, Fixture const& xrp)
    {
        testcase("withdraw one drop in investment at a 50% fee");
        StagedVault staged = depositedVault(env, xrp.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee50Pct);
        expectVerdict(
            checkWithdraw(*this, env, xrp.vaultKeylet, xrp.holder, staged, jtx::drops(1)).ter,
            tecPRECISION_LOSS);
    }

    // IOU: a 50% fee on one grid unit (1e-6) leaves 5e-7, representable but below the vault grid.
    void
    testWithdrawFeeLeavesSubGridPayout(jtx::Env& env, Fixture const& f)
    {
        testcase("withdraw one grid unit in investment at a 50% fee");
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee50Pct);
        expectVerdict(
            checkWithdraw(*this, env, f.vaultKeylet, f.holder, staged, f.asset(Number{1, -6})).ter,
            tecPRECISION_LOSS);
    }

    // Clawback has no phase or fee logic: the issuer recovers the full amount during Investment.
    void
    testClawbackInInvestment(jtx::Env& env, Fixture const& f)
    {
        testcase("clawback in investment with a fee");
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee5Pct);
        STAmount const amount = f.asset(400);
        AppliedVaultTx const cpp = applyStaged(
            env,
            f.vaultKeylet,
            f.holder,
            staged,
            jtx::Vault::clawback(
                {.issuer = f.issuer,
                 .id = f.vaultKeylet.key,
                 .holder = f.holder,
                 .amount = amount}));
        LeanVaultResult const lean = leanVaultClawback(
            cpp.pre,
            amount,
            shareAmount(env, f.vaultKeylet, *staged.holderShares),
            *staged.holderShares == staged.sharesTotal);
        expectVerdict(expectAgree(*this, sampleText(staged, amount), cpp, lean), tesSUCCESS);
        Number const recovered = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;
        BEAST_EXPECTS(recovered == Number{400}, "recovered " + to_string(recovered));
    }

    // VaultSet has no phase logic: the owner caps a closed-ended vault during Investment.
    void
    testSetInInvestment(jtx::Env& env, Fixture const& f)
    {
        testcase("set assets maximum in investment");
        StagedVault staged = depositedVault(env, f.vaultKeylet, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee5Pct);
        Number const cap{5'000};
        auto tx = jtx::Vault::set({.owner = f.owner, .id = f.vaultKeylet.key});
        tx[sfAssetsMaximum] = cap;
        AppliedVaultTx const cpp = applyStaged(env, f.vaultKeylet, f.holder, staged, tx);

        auto const lean = leanCanVaultUpdate(cpp.pre, cap);
        expectLawful(lean);
        LeanUpdateResult const updated = leanVaultUpdate(cpp.pre, cap);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean canVaultUpdate error");
        expectTer(lean.ter, cpp.ter, tesSUCCESS);
        BEAST_EXPECTS(!updated.leanError.has_value(), "lean update error");
        BEAST_EXPECTS(
            updated.vault.assetsMaximum == cpp.post.assetsMaximum && cpp.post.assetsMaximum == cap,
            "stored cap " + (cpp.post.assetsMaximum ? to_string(*cpp.post.assetsMaximum) : "none"));
    }

    // VaultDelete has no phase logic: an empty closed-ended vault is deleted during Investment.
    void
    testDeleteInInvestment()
    {
        using namespace jtx;
        testcase("delete an empty closed-ended vault in investment");

        Env env(*this);
        auto const f = setUp(env, VaultPhase::Investment, kFee5Pct, Number{0});

        Vault const state = readVaultState(env, f.vaultKeylet, f.asset.raw());
        auto const lean = leanCanVaultDelete(state);
        expectLawful(lean);

        env(jtx::Vault::del({.owner = f.owner, .id = f.vaultKeylet.key}), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(!lean.leanError.has_value(), "lean canVaultDelete error");
        expectTer(lean.ter, cppTer, tesSUCCESS);
        BEAST_EXPECT(!env.le(f.vaultKeylet));
    }

    // ---- Phase date sweeps ---------------------------------------------------------------------

    // Dates of a closed-ended vault whose subscription date is P + offset (P the parent close
    // time).
    template <class Row>
    static StagedVault&
    subscriptionAt(StagedVault& s, std::uint32_t p, Row const& c)
    {
        s.subscriptionDate = static_cast<std::uint32_t>(p + c.offset);
        s.redemptionDate = static_cast<std::uint32_t>(p + c.offset + c.gap);
        return s;
    }

    // Dates of a closed-ended vault whose redemption date is P + offset.
    template <class Row>
    static StagedVault&
    redemptionAt(StagedVault& s, std::uint32_t p, Row const& c)
    {
        s.subscriptionDate = static_cast<std::uint32_t>(p + c.offset - c.gap);
        s.redemptionDate = static_cast<std::uint32_t>(p + c.offset);
        return s;
    }

    // A vault at price 1 with 2e9 grid units, the holder owning all but one share (no final
    // withdrawal, no loss waiver).
    static StagedVault
    withdrawVault(jtx::Env& env, Keylet const& vault)
    {
        StagedVault s = depositedVault(env, vault, 2 * kOrdinaryUnits);
        s.holderShares = 2 * kOrdinaryUnits - 1;
        return s;
    }

    // Subscription date: a plain deposit of one unit is accepted while P <= subscription date and
    // tecEXPIRED after it. Rows put the subscription date at P + offset.
    void
    testDepositSubscriptionSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            beginCase(("deposit " + vaultName(env, vault) + " subscription date-Sweep").c_str());
            std::uint32_t const p = parentCloseTime(env);
            runAroundCusp(closed_ended_sweep::kPhaseDateCases, [&](auto const& c) {
                StagedVault staged{
                    .available = gridUnits(env, vault, kOrdinaryUnits),
                    .sharesTotal = static_cast<std::uint64_t>(kOrdinaryUnits)};
                return checkDeposit(
                    env, vault, depositor, subscriptionAt(staged, p, c), gridUnits(env, vault, 1));
            });
        }
    }

    // End of Subscription, no early-exit fee field: withdrawing one unit is accepted while
    // P <= subscription date and tecTOO_SOON in Investment. Subscription date at P + offset.
    void
    testWithdrawSubscriptionEndSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " subscription end-Sweep").c_str());
            std::uint32_t const p = parentCloseTime(env);
            runAroundCusp(closed_ended_sweep::kPhaseDateCases, [&](auto const& c) {
                StagedVault staged = withdrawVault(env, vault);
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           subscriptionAt(staged, p, c),
                           gridUnits(env, vault, 1))
                    .ter;
            });
        }
    }

    // Start of Redemption, no early-exit fee field: tecTOO_SOON up to the last second of
    // Investment (P = redemption date - 1), accepted from P = redemption date. Redemption date at
    // P + offset.
    void
    testWithdrawRedemptionStartSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " redemption start-Sweep").c_str());
            std::uint32_t const p = parentCloseTime(env);
            runAroundCusp(closed_ended_sweep::kPhaseDateCases, [&](auto const& c) {
                StagedVault staged = withdrawVault(env, vault);
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           redemptionAt(staged, p, c),
                           gridUnits(env, vault, 1))
                    .ter;
            });
        }
    }

    // With an early-exit fee rate the vault never refuses a withdrawal; the fee is charged only in
    // Investment, so the payout changes at both dates (no verdict change: payouts compared).
    void
    testWithdrawFeePhaseSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " fee phase-Sweep").c_str());
            std::uint32_t const p = parentCloseTime(env);
            STAmount const amount = gridUnits(env, vault, kOrdinaryUnits);
            auto const check = [&](bool atRedemption) {
                return [&, atRedemption](closed_ended_sweep::FeePhaseCusp const& c) {
                    StagedVault staged = withdrawVault(env, vault);
                    staged.earlyExitFeeRate = c.rate;
                    return checkWithdraw(
                               *this,
                               env,
                               vault,
                               holder,
                               atRedemption ? redemptionAt(staged, p, c)
                                            : subscriptionAt(staged, p, c),
                               amount)
                        .ter;
                };
            };
            runAroundCusp(closed_ended_sweep::kFeePhaseCases, check(false), false);
            runAroundCusp(closed_ended_sweep::kFeePhaseCases, check(true), false);
        }
    }

    void
    runTests() override
    {
        using namespace jtx;
        using namespace std::chrono_literals;

        // One ledger holding a vault per asset; every staged sample (old tests and sweeps) runs on
        // a throwaway view of it.
        Env env{*this};
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        Account const depositor{"depositor"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.fund(XRP(9'500'000'000), depositor);
        env.close();
        // Clawback must be enabled while the issuer has no trust line yet.
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();
        // Staged dates reach a 30-year gap before the parent close time, which starts near 0.
        env.close(env.now() + 1'000'000'000s);

        PrettyAsset const xrp{xrpIssue(), 1'000'000};
        PrettyAsset const iou = issuer["USD"];
        // An IOU holder and an owner that are not the issuer, as in the old Env-based setUp.
        env(trust(owner, iou(Number{1, 10})));
        env(trust(holder, iou(Number{1, 10})));
        env.close();
        env(pay(issuer, owner, iou(10'000)));
        env(pay(issuer, holder, iou(1'000'000'000)));
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer, depositor, mpt(9'200'000'000'000'000)));
        env.close();

        Keylet const xrpVault = createSweepVault(env, owner, depositor, xrp);
        Keylet const mptVault = createSweepVault(env, owner, depositor, mpt);
        Keylet const iouScale0Vault = createSweepVault(env, owner, issuer, iou, 0);
        Keylet const iouScale6Vault = createSweepVault(env, owner, issuer, iou, 6);
        Keylet const iouScale10Vault = createSweepVault(env, owner, issuer, iou, 10);
        // The old tests' holder needs its own share MPToken in the IOU vault.
        env(jtx::Vault::deposit(
            {.depositor = holder,
             .id = iouScale6Vault.key,
             .amount = gridUnits(env, iouScale6Vault, 1)}));
        env.close();

        Fixture const f{owner, issuer, holder, iou, iouScale6Vault};
        Fixture const x{owner, issuer, depositor, xrp, xrpVault};

        // Deposits
        testDeposit(env, f, VaultPhase::NoPhase, false, tesSUCCESS);
        testDeposit(env, f, VaultPhase::Subscription, false, tesSUCCESS);
        testDeposit(env, f, VaultPhase::Subscription, false, tesSUCCESS, kOnDate);
        testDeposit(env, f, VaultPhase::Investment, false, tecEXPIRED);
        testDeposit(env, f, VaultPhase::Redemption, false, tecEXPIRED, kOnDate);
        testDeposit(env, f, VaultPhase::Redemption, false, tecEXPIRED);
        // Donations are not subject to the phase check.
        testDeposit(env, f, VaultPhase::NoPhase, true, tesSUCCESS);
        testDeposit(env, f, VaultPhase::Subscription, true, tesSUCCESS);
        testDeposit(env, f, VaultPhase::Investment, true, tesSUCCESS);
        testDeposit(env, f, VaultPhase::Redemption, true, tesSUCCESS);

        // Withdrawals without an early-exit fee field: only Investment is closed.
        testWithdraw(env, f, VaultPhase::NoPhase, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(env, f, VaultPhase::Subscription, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(
            env, f, VaultPhase::Subscription, std::nullopt, tesSUCCESS, Number{400}, kOnDate);
        testWithdraw(env, f, VaultPhase::Investment, std::nullopt, tecTOO_SOON);
        testWithdraw(
            env, f, VaultPhase::Redemption, std::nullopt, tesSUCCESS, Number{400}, kOnDate);
        testWithdraw(env, f, VaultPhase::Redemption, std::nullopt, tesSUCCESS, Number{400});

        // A zero fee rate opens Investment without charging anything.
        testWithdraw(env, f, VaultPhase::Investment, 0, tesSUCCESS, Number{400});

        // A 5% fee applies in Investment only: 400 - 20 = 380.
        testWithdraw(env, f, VaultPhase::Subscription, kFee5Pct, tesSUCCESS, Number{400});
        testWithdraw(env, f, VaultPhase::Subscription, kFee5Pct, tesSUCCESS, Number{400}, kOnDate);
        testWithdraw(env, f, VaultPhase::Investment, kFee5Pct, tesSUCCESS, Number{380});
        testWithdraw(env, f, VaultPhase::Redemption, kFee5Pct, tesSUCCESS, Number{400}, kOnDate);
        testWithdraw(env, f, VaultPhase::Redemption, kFee5Pct, tesSUCCESS, Number{400});

        // A 100% fee burns the shares and pays nothing.
        testWithdraw(env, f, VaultPhase::Investment, kFee100Pct, tesSUCCESS, Number{0});

        testWithdrawBySharesInInvestment(env, f);
        testWithdrawAllSharesInInvestment(env, f);
        testWithdrawGrossOverAvailable(env, f, 0, tecINSUFFICIENT_FUNDS);
        testWithdrawGrossOverAvailable(env, f, kFee5Pct, tesSUCCESS);
        // The net payout (380) itself exceeds what is available.
        testWithdrawGrossOverAvailable(env, f, kFee5Pct, tecINSUFFICIENT_FUNDS, Number{300});
        testWithdrawInexactFee(env, f);
        testWithdrawFeeConsumesPayout(env, x);
        testWithdrawFeeLeavesSubGridPayout(env, f);

        testClawbackInInvestment(env, f);
        testSetInInvestment(env, f);
        // Needs an empty vault with no other share holders: its own Env.
        testDeleteInInvestment();

        SweepVaults const all{
            {xrpVault, depositor},
            {mptVault, depositor},
            {iouScale0Vault, issuer},
            {iouScale6Vault, issuer},
            {iouScale10Vault, issuer}};
        testDepositSubscriptionSweep(env, all);
        testWithdrawSubscriptionEndSweep(env, all);
        testWithdrawRedemptionStartSweep(env, all);
        testWithdrawFeePhaseSweep(env, all);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClosedEnded, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
