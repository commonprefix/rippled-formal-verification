#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultDeleteFFI.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultSetFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/flags.h>
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

namespace xrpl::test::formal_verification {

// Differential tests of the vault lifecycle: every VaultDeposit and VaultWithdraw branch that
// depends on the vault phase (Subscription, Investment, Redemption) or on the early-exit fee, with
// the open-ended vault (no phase) as the reference row of each matrix. Clawback, set and delete
// have no phase logic; one closed-ended case each checks that both sides agree on that.
class LeanVaultClosedEnded_test : public LeanSuite
{
    // The parent close time of the transaction's ledger relative to the schedule. Subscription
    // ends strictly after the subscription date, Redemption starts at the redemption date.
    enum class Phase : std::uint8_t {
        None,
        Subscription,
        SubscriptionDate,  // exactly at the subscription date: still Subscription
        Investment,
        RedemptionDate,  // exactly at the redemption date: already Redemption
        Redemption
    };

    static std::string
    phaseName(Phase phase)
    {
        switch (phase)
        {
            case Phase::None:
                return "open-ended";
            case Phase::Subscription:
                return "subscription";
            case Phase::SubscriptionDate:
                return "at the subscription date";
            case Phase::Investment:
                return "investment";
            case Phase::RedemptionDate:
                return "at the redemption date";
            case Phase::Redemption:
                return "redemption";
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

    // Long enough for the creation and seed-deposit ledgers (5 s each) to stay in Subscription.
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

    // Fund the accounts, create the vault (closed-ended unless `phase` is None, with the given
    // early-exit fee rate), let the holder seed it during Subscription, then advance into `phase`.
    // The schedule dates are multiples of the close-time resolution, so the boundary phases can be
    // reached exactly.
    Fixture
    setUp(
        jtx::Env& env,
        Phase phase,
        std::optional<std::uint32_t> earlyExitFeeRate,
        Number const& seed,
        bool xrp = false)
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
        if (phase != Phase::None)
        {
            createArgs.vaultKind = std::to_underlying(VaultKind::ClosedEnded);
            createArgs.subscriptionDate = timeCount(subscriptionDate);
            createArgs.redemptionDate = timeCount(redemptionDate);
            createArgs.earlyExitFeeRate = earlyExitFeeRate;
        }
        auto const [createTx, vaultKeylet] = vault.create(createArgs);
        env(createTx);
        env.close();

        if (seed != Number{0})
        {
            env(jtx::Vault::deposit(
                    {.depositor = holder, .id = vaultKeylet.key, .amount = asset(seed)}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }

        switch (phase)
        {
            case Phase::SubscriptionDate:
                closeOn(env, subscriptionDate);
                break;
            case Phase::Investment:
                env.close(subscriptionDate + 1s);
                break;
            case Phase::RedemptionDate:
                closeOn(env, redemptionDate);
                break;
            case Phase::Redemption:
                env.close(redemptionDate + 1s);
                break;
            default:
                break;
        }
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

    void
    expectSameVault(Vault const& lean, Vault const& cpp)
    {
        auto const check = [&](char const* name, Number const& l, Number const& c) {
            BEAST_EXPECTS(
                l == c, std::string(name) + " lean=" + to_string(l) + " cpp=" + to_string(c));
        };
        check("assetsTotal", lean.assetsTotal, cpp.assetsTotal);
        check("assetsAvailable", lean.assetsAvailable, cpp.assetsAvailable);
        check("assetsDeployed", lean.assetsDeployed, cpp.assetsDeployed);
        check("assetsReserved", lean.assetsReserved, cpp.assetsReserved);
        check("sharesTotal", lean.sharesTotal, cpp.sharesTotal);
        check("lossUnrealized", lean.lossUnrealized, cpp.lossUnrealized);
        check("yieldUnrealized", lean.yieldUnrealized, cpp.yieldUnrealized);
    }

    void
    compareDeposit(
        jtx::Env& env,
        Fixture const& f,
        jtx::Account const& depositor,
        STAmount const& amount,
        bool isDonation,
        TER expected)
    {
        using namespace jtx;
        Vault const before = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LeanVaultResult const lean =
            leanVaultDeposit(before, amount, isDonation, parentCloseTime(env));
        expectLawful(lean);

        jtx::Vault::DepositArgs args{
            .depositor = depositor, .id = f.vaultKeylet.key, .amount = amount};
        if (isDonation)
            args.flags = tfVaultDonate;
        env(jtx::Vault::deposit(args), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        Vault const cpp = readVaultState(env, f.vaultKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!lean.leanError.has_value(), "lean deposit error");
        expectTer(lean.error.value_or(tesSUCCESS), cppTer, expected);
        if (cppTer == tesSUCCESS && !lean.leanError && !lean.error)
            expectSameVault(lean.vault, cpp);
    }

    // The holder withdraws `amount` (assets or shares). On success the vault states must match and
    // the model payout must be what left the vault: an early-exit fee stays behind.
    void
    compareWithdraw(
        jtx::Env& env,
        Fixture const& f,
        STAmount const& amount,
        TER expected,
        std::optional<Number> const& expectedPayout = std::nullopt)
    {
        using namespace jtx;
        Vault const before = readVaultState(env, f.vaultKeylet, f.asset.raw());
        bool const byShares = amount.asset() != f.asset.raw();
        bool const waiveUnrealizedLoss = holderOwnsAllShares(env, f.vaultKeylet, f.holder);
        LeanVaultResult const lean = leanVaultWithdraw(
            before,
            amount,
            byShares,
            parentCloseTime(env),
            waiveUnrealizedLoss,
            Number{fetchHolderShares(env, f.vaultKeylet, f.holder)});
        expectLawful(lean);

        env(jtx::Vault::withdraw(
                {.depositor = f.holder, .id = f.vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        Vault const cpp = readVaultState(env, f.vaultKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!lean.leanError.has_value(), "lean withdraw error");
        expectTer(lean.error.value_or(tesSUCCESS), cppTer, expected);
        if (cppTer != tesSUCCESS || lean.leanError || lean.error)
            return;

        expectSameVault(lean.vault, cpp);
        Number const cppPayout = before.assetsAvailable - cpp.assetsAvailable;
        BEAST_EXPECTS(
            Number{lean.assets} == cppPayout,
            "payout lean=" + to_string(Number{lean.assets}) + " cpp=" + to_string(cppPayout));
        if (expectedPayout)
        {
            BEAST_EXPECTS(
                cppPayout == *expectedPayout,
                "payout " + to_string(cppPayout) + " expected " + to_string(*expectedPayout));
        }
    }

    // Deposit matrix: a plain deposit is rejected once the vault is past Subscription, a donation
    // never is.
    void
    testDeposit(Phase phase, bool isDonation, TER expected)
    {
        using namespace jtx;
        testcase((isDonation ? "donate " : "deposit ") + phaseName(phase));

        Env env(*this);
        auto const f = setUp(env, phase, std::nullopt, Number{1'000});
        compareDeposit(env, f, isDonation ? f.owner : f.holder, f.asset(100), isDonation, expected);
    }

    // Withdraw matrix: a withdrawal by assets of 400 from a 1000 seed. Only the Investment phase
    // of a vault with an early-exit fee rate (even zero) charges the fee or, without the field,
    // rejects the withdrawal.
    void
    testWithdraw(
        Phase phase,
        std::optional<std::uint32_t> earlyExitFeeRate,
        TER expected,
        std::optional<Number> const& expectedPayout = std::nullopt)
    {
        using namespace jtx;
        testcase("withdraw " + phaseName(phase) + ", " + feeName(earlyExitFeeRate));

        Env env(*this);
        auto const f = setUp(env, phase, earlyExitFeeRate, Number{1'000});
        compareWithdraw(env, f, f.asset(400), expected, expectedPayout);
    }

    // By shares: 400 of the 1000 shares (scale 6: 4e8) at a 5% fee pay 380.
    void
    testWithdrawBySharesInInvestment()
    {
        using namespace jtx;
        testcase("withdraw by shares in investment at a 5% fee");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee5Pct, Number{1'000});
        STAmount const shares{fetchHolderShares(env, f.vaultKeylet, f.holder).asset(), 400'000'000};
        compareWithdraw(env, f, shares, tesSUCCESS, Number{380});
    }

    // A final withdrawal (all outstanding shares) skips the fee even during Investment.
    void
    testWithdrawAllSharesInInvestment()
    {
        using namespace jtx;
        testcase("withdraw all shares in investment with a fee");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee5Pct, Number{1'000});
        STAmount const allShares = fetchHolderShares(env, f.vaultKeylet, f.holder);
        compareWithdraw(env, f, allShares, tesSUCCESS, Number{1'000});
    }

    // Availability is checked against the gross amount without a fee and against the net payout
    // with one: 610 of the 1000 are deployed (staged), so withdrawing 400 fails at a zero rate and
    // pays 380 at 5%.
    void
    testWithdrawGrossOverAvailable(
        std::uint32_t earlyExitFeeRate,
        TER expected,
        Number const& available = Number{390})
    {
        using namespace jtx;
        testcase(
            "withdraw 400 with " + to_string(available) + " available at " +
            feeName(earlyExitFeeRate));

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, earlyExitFeeRate, Number{1'000});
        BEAST_EXPECT(
            updateVaultState(env, f.vaultKeylet, Number{1'000}, available, 1'000'000'000ULL));
        compareWithdraw(
            env,
            f,
            f.asset(400),
            expected,
            expected == tesSUCCESS ? std::optional<Number>{Number{380}} : std::nullopt);
    }

    // A 16-digit amount at a 3.333% rate: the fee needs more digits than Number keeps, so the
    // upward fee and downward subtraction must round the same way on both sides.
    void
    testWithdrawInexactFee()
    {
        using namespace jtx;
        testcase("withdraw a 16-digit amount at an inexact fee rate");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, 3'333, Number{2, 9});
        compareWithdraw(env, f, f.asset(Number{1'234'567'891'234'567LL, -6}), tesSUCCESS);
    }

    // XRP: a 50% fee on one drop leaves half a drop, which is zero in drops.
    void
    testWithdrawFeeConsumesPayout()
    {
        using namespace jtx;
        testcase("withdraw one drop in investment at a 50% fee");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee50Pct, Number{1'000}, true);
        compareWithdraw(env, f, drops(1), tecPRECISION_LOSS);
    }

    // IOU: a 50% fee on one grid unit (1e-6) leaves 5e-7, representable but below the vault grid.
    void
    testWithdrawFeeLeavesSubGridPayout()
    {
        using namespace jtx;
        testcase("withdraw one grid unit in investment at a 50% fee");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee50Pct, Number{1'000});
        compareWithdraw(env, f, f.asset(Number{1, -6}), tecPRECISION_LOSS);
    }

    // Clawback has no phase or fee logic: the issuer recovers the full amount during Investment.
    void
    testClawbackInInvestment()
    {
        using namespace jtx;
        testcase("clawback in investment with a fee");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee5Pct, Number{1'000});
        STAmount const amount = f.asset(400);

        Vault const before = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LeanVaultResult const lean = leanVaultClawback(
            before,
            amount,
            fetchHolderShares(env, f.vaultKeylet, f.holder),
            holderOwnsAllShares(env, f.vaultKeylet, f.holder));
        expectLawful(lean);

        env(jtx::Vault::clawback(
                {.issuer = f.issuer,
                 .id = f.vaultKeylet.key,
                 .holder = f.holder,
                 .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Vault const cpp = readVaultState(env, f.vaultKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!lean.leanError.has_value(), "lean clawback error");
        expectTer(lean.error.value_or(tesSUCCESS), cppTer, tesSUCCESS);
        if (cppTer != tesSUCCESS || lean.leanError || lean.error)
            return;
        expectSameVault(lean.vault, cpp);
        Number const recovered = before.assetsAvailable - cpp.assetsAvailable;
        BEAST_EXPECTS(recovered == Number{400}, "recovered " + to_string(recovered));
    }

    // VaultSet has no phase logic: the owner caps a closed-ended vault during Investment.
    void
    testSetInInvestment()
    {
        using namespace jtx;
        testcase("set assets maximum in investment");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee5Pct, Number{1'000});
        Number const cap{5'000};

        Vault const state = readVaultState(env, f.vaultKeylet, f.asset.raw());
        auto const lean = leanCanVaultUpdate(state, cap);
        expectLawful(lean);
        LeanUpdateResult const updated = leanVaultUpdate(state, cap);

        auto tx = jtx::Vault::set({.owner = f.owner, .id = f.vaultKeylet.key});
        tx[sfAssetsMaximum] = cap;
        env(tx, jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Vault const cpp = readVaultState(env, f.vaultKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!lean.leanError.has_value(), "lean canVaultUpdate error");
        expectTer(lean.ter, cppTer, tesSUCCESS);
        BEAST_EXPECTS(!updated.leanError.has_value(), "lean update error");
        BEAST_EXPECTS(
            updated.vault.assetsMaximum == cpp.assetsMaximum && cpp.assetsMaximum == cap,
            "stored cap " + (cpp.assetsMaximum ? to_string(*cpp.assetsMaximum) : "none"));
    }

    // VaultDelete has no phase logic: an empty closed-ended vault is deleted during Investment.
    void
    testDeleteInInvestment()
    {
        using namespace jtx;
        testcase("delete an empty closed-ended vault in investment");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee5Pct, Number{0});

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

    void
    runTests() override
    {
        // Deposits
        testDeposit(Phase::None, false, tesSUCCESS);
        testDeposit(Phase::Subscription, false, tesSUCCESS);
        testDeposit(Phase::SubscriptionDate, false, tesSUCCESS);
        testDeposit(Phase::Investment, false, tecEXPIRED);
        testDeposit(Phase::RedemptionDate, false, tecEXPIRED);
        testDeposit(Phase::Redemption, false, tecEXPIRED);
        // Donations are not subject to the phase check.
        testDeposit(Phase::None, true, tesSUCCESS);
        testDeposit(Phase::Subscription, true, tesSUCCESS);
        testDeposit(Phase::Investment, true, tesSUCCESS);
        testDeposit(Phase::Redemption, true, tesSUCCESS);

        // Withdrawals without an early-exit fee field: only Investment is closed.
        testWithdraw(Phase::None, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(Phase::Subscription, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(Phase::SubscriptionDate, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(Phase::Investment, std::nullopt, tecTOO_SOON);
        testWithdraw(Phase::RedemptionDate, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(Phase::Redemption, std::nullopt, tesSUCCESS, Number{400});

        // A zero fee rate opens Investment without charging anything.
        testWithdraw(Phase::Investment, 0, tesSUCCESS, Number{400});

        // A 5% fee applies in Investment only: 400 - 20 = 380.
        testWithdraw(Phase::Subscription, kFee5Pct, tesSUCCESS, Number{400});
        testWithdraw(Phase::SubscriptionDate, kFee5Pct, tesSUCCESS, Number{400});
        testWithdraw(Phase::Investment, kFee5Pct, tesSUCCESS, Number{380});
        testWithdraw(Phase::RedemptionDate, kFee5Pct, tesSUCCESS, Number{400});
        testWithdraw(Phase::Redemption, kFee5Pct, tesSUCCESS, Number{400});

        // A 100% fee burns the shares and pays nothing.
        testWithdraw(Phase::Investment, kFee100Pct, tesSUCCESS, Number{0});

        testWithdrawBySharesInInvestment();
        testWithdrawAllSharesInInvestment();
        testWithdrawGrossOverAvailable(0, tecINSUFFICIENT_FUNDS);
        testWithdrawGrossOverAvailable(kFee5Pct, tesSUCCESS);
        // The net payout (380) itself exceeds what is available.
        testWithdrawGrossOverAvailable(kFee5Pct, tecINSUFFICIENT_FUNDS, Number{300});
        testWithdrawInexactFee();
        testWithdrawFeeConsumesPayout();
        testWithdrawFeeLeavesSubGridPayout();

        testClawbackInInvestment();
        testSetInInvestment();
        testDeleteInInvestment();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClosedEnded, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
