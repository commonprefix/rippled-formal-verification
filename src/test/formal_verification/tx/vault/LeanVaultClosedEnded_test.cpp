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
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

// Differential tests of the vault lifecycle: every VaultDeposit and VaultWithdraw branch that
// depends on the vault phase (Subscription, Investment, Redemption) or on the early-exit fee, with
// the open-ended vault (no phase) as the reference row of each matrix. Clawback, set and delete
// have no phase logic; one closed-ended case each checks that both sides agree on that.
class LeanVaultClosedEnded_test : public LeanSuite
{
    enum class Phase : std::uint8_t { None, Subscription, Investment, Redemption };

    static std::string
    phaseName(Phase phase)
    {
        switch (phase)
        {
            case Phase::None:
                return "open-ended";
            case Phase::Subscription:
                return "subscription";
            case Phase::Investment:
                return "investment";
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

    // Fund the accounts, create the vault (closed-ended unless `phase` is None, with the given
    // early-exit fee rate), let the holder seed it during Subscription, then advance into `phase`.
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
            env(trust(owner, asset(1'000'000)));
            env(trust(holder, asset(1'000'000)));
            env.close();
            env(pay(issuer, owner, asset(10'000)));
            env(pay(issuer, holder, asset(10'000)));
            env.close();
        }

        jtx::Vault vault{env};
        std::optional<Keylet> vaultKeylet;
        NetClock::time_point subscriptionDate{};
        if (phase == Phase::None)
        {
            auto const [tx, keylet] = vault.create({.owner = owner, .asset = asset.raw()});
            env(tx);
            vaultKeylet = keylet;
        }
        else
        {
            auto const [tx, keylet, sub] = vault.createClosedEnded(
                {.owner = owner,
                 .asset = asset.raw(),
                 .subscriptionOffset = kSubscriptionOffset,
                 .investmentWindow = kInvestmentWindow,
                 .earlyExitFeeRate = earlyExitFeeRate});
            env(tx);
            vaultKeylet = keylet;
            subscriptionDate = sub;
        }
        env.close();

        if (seed != Number{0})
        {
            env(jtx::Vault::deposit(
                    {.depositor = holder, .id = vaultKeylet->key, .amount = asset(seed)}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }

        switch (phase)
        {
            case Phase::Investment:
                vault.closePastSubscription(subscriptionDate);
                break;
            case Phase::Redemption:
                env.close(subscriptionDate + kInvestmentWindow + 1s);
                break;
            default:
                break;
        }
        return {owner, issuer, holder, asset, *vaultKeylet};
    }

    static MPTIssue
    shareIssue(jtx::Env& env, Keylet const& vaultKeylet)
    {
        return MPTIssue{env.le(vaultKeylet)->at(sfShareMPTID)};
    }

    static STAmount
    holderShares(jtx::Env& env, Keylet const& vaultKeylet, jtx::Account const& holder)
    {
        auto const share = shareIssue(env, vaultKeylet);
        auto const sleToken = env.le(keylet::mptoken(share.getMptID(), holder.id()));
        return STAmount{share, sleToken ? sleToken->at(sfMPTAmount) : 0};
    }

    // A model raise surfaces as tefEXCEPTION, matching the C++ transactor.
    static TER
    leanTer(LeanVaultResult const& r)
    {
        if (r.leanError)
            return tefEXCEPTION;
        return r.error.value_or(tesSUCCESS);
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
        check("sharesTotal", lean.sharesTotal, cpp.sharesTotal);
        check("lossUnrealized", lean.lossUnrealized, cpp.lossUnrealized);
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
        env.close();

        expectTer(leanTer(lean), cppTer, expected);
        if (cppTer == tesSUCCESS && leanTer(lean) == tesSUCCESS)
            expectSameVault(lean.vault, readVaultState(env, f.vaultKeylet, f.asset.raw()));
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
        LeanVaultResult const lean =
            leanVaultWithdraw(before, amount, byShares, parentCloseTime(env));
        expectLawful(lean);

        env(jtx::Vault::withdraw(
                {.depositor = f.holder, .id = f.vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        expectTer(leanTer(lean), cppTer, expected);
        if (cppTer != tesSUCCESS || leanTer(lean) != tesSUCCESS)
            return;

        Vault const after = readVaultState(env, f.vaultKeylet, f.asset.raw());
        expectSameVault(lean.vault, after);
        Number const cppPayout = before.assetsAvailable - after.assetsAvailable;
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

    // A final withdrawal (all outstanding shares) skips the fee even during Investment.
    void
    testWithdrawAllSharesInInvestment()
    {
        using namespace jtx;
        testcase("withdraw all shares in investment with a fee");

        Env env(*this);
        auto const f = setUp(env, Phase::Investment, kFee5Pct, Number{1'000});
        STAmount const allShares = holderShares(env, f.vaultKeylet, f.holder);
        compareWithdraw(env, f, allShares, tesSUCCESS, Number{1'000});
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
        LeanVaultResult const lean =
            leanVaultClawback(before, amount, holderShares(env, f.vaultKeylet, f.holder));
        expectLawful(lean);

        env(jtx::Vault::clawback(
                {.issuer = f.issuer,
                 .id = f.vaultKeylet.key,
                 .holder = f.holder,
                 .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        expectTer(leanTer(lean), cppTer, tesSUCCESS);
        if (cppTer != tesSUCCESS || leanTer(lean) != tesSUCCESS)
            return;
        Vault const after = readVaultState(env, f.vaultKeylet, f.asset.raw());
        expectSameVault(lean.vault, after);
        Number const recovered = before.assetsAvailable - after.assetsAvailable;
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

        auto tx = jtx::Vault::set({.owner = f.owner, .id = f.vaultKeylet.key});
        tx[sfAssetsMaximum] = cap;
        env(tx, jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        expectTer(lean.leanError ? tefEXCEPTION : lean.ter, cppTer, tesSUCCESS);
        Number const stored = env.le(f.vaultKeylet)->at(sfAssetsMaximum);
        BEAST_EXPECTS(stored == cap, "stored cap " + to_string(stored));
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

        expectTer(lean.leanError ? tefEXCEPTION : lean.ter, cppTer, tesSUCCESS);
        BEAST_EXPECT(!env.le(f.vaultKeylet));
    }

    void
    runTests() override
    {
        // Deposits
        testDeposit(Phase::None, false, tesSUCCESS);
        testDeposit(Phase::Subscription, false, tesSUCCESS);
        testDeposit(Phase::Investment, false, tecEXPIRED);
        testDeposit(Phase::Redemption, false, tecEXPIRED);
        // Donations are not subject to the phase check.
        testDeposit(Phase::None, true, tesSUCCESS);
        testDeposit(Phase::Subscription, true, tesSUCCESS);
        testDeposit(Phase::Investment, true, tesSUCCESS);
        testDeposit(Phase::Redemption, true, tesSUCCESS);

        // Withdrawals without an early-exit fee field: only Investment is closed.
        testWithdraw(Phase::None, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(Phase::Subscription, std::nullopt, tesSUCCESS, Number{400});
        testWithdraw(Phase::Investment, std::nullopt, tecTOO_SOON);
        testWithdraw(Phase::Redemption, std::nullopt, tesSUCCESS, Number{400});

        // A zero fee rate opens Investment without charging anything.
        testWithdraw(Phase::Investment, 0, tesSUCCESS, Number{400});

        // A 5% fee applies in Investment only: 400 - 20 = 380.
        testWithdraw(Phase::Subscription, kFee5Pct, tesSUCCESS, Number{400});
        testWithdraw(Phase::Investment, kFee5Pct, tesSUCCESS, Number{380});
        testWithdraw(Phase::Redemption, kFee5Pct, tesSUCCESS, Number{400});

        // A 100% fee burns the shares and pays nothing.
        testWithdraw(Phase::Investment, kFee100Pct, tesSUCCESS, Number{0});

        testWithdrawAllSharesInInvestment();
        testWithdrawFeeConsumesPayout();
        testWithdrawFeeLeavesSubGridPayout();

        testClawbackInInvestment();
        testSetInInvestment();
        testDeleteInInvestment();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClosedEnded, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
