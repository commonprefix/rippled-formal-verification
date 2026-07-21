#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultClawback_test : public LeanSuite
{
    static MPTIssue
    shareIssue(jtx::Env& env, Keylet const& vaultKeylet)
    {
        return MPTIssue{env.le(vaultKeylet)->at(sfShareMPTID)};
    }

    void
    compareClawbackAsset(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& issuer,
        jtx::Account const& holder,
        Asset const& asset,
        STAmount const& amount,
        TER expected)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        LeanClawbackResult const clawback = leanVaultClawback(state, amount);

        env(Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!clawback.threw, "lean clawback raised");

        TER const leanTer = clawback.error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            leanTer == expected,
            std::string("lean=") + transToken(leanTer) + " expected " + transToken(expected));

        if (cppTer != tesSUCCESS)
            return;

        auto const newVaultSle = env.le(vaultKeylet);
        auto const issuanceKeylet = keylet::mptIssuance(newVaultSle->at(sfShareMPTID));
        Number const cppAssetsTotal = newVaultSle->at(sfAssetsTotal);
        Number const cppAssetsAvailable = newVaultSle->at(sfAssetsAvailable);
        Number const cppSharesTotal{
            static_cast<std::int64_t>(env.le(issuanceKeylet)->at(sfOutstandingAmount))};
        BEAST_EXPECTS(
            clawback.vault.assetsTotal == cppAssetsTotal,
            "assetsTotal lean=" + to_string(clawback.vault.assetsTotal) +
                " cpp=" + to_string(cppAssetsTotal));
        BEAST_EXPECTS(
            clawback.vault.assetsAvailable == cppAssetsAvailable,
            "assetsAvailable lean=" + to_string(clawback.vault.assetsAvailable) +
                " cpp=" + to_string(cppAssetsAvailable));
        BEAST_EXPECTS(
            clawback.vault.sharesTotal == cppSharesTotal,
            "sharesTotal lean=" + to_string(clawback.vault.sharesTotal) +
                " cpp=" + to_string(cppSharesTotal));
    }

    void
    testClawbackAsset(std::int64_t seed, std::int64_t amount, TER expected)
    {
        using namespace jtx;
        testcase("clawback MPT asset " + std::to_string(amount) + " from " + std::to_string(seed));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(seed)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = asset(seed)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(amount), expected);
    }

    // MPT vault where the owner donates assets without shares, drifting NAV off 1:1 so the
    // clawback conversions round. The issuer then claws `clawAmount` from the holder.
    void
    testClawbackDrifted(
        std::int64_t deposit,
        std::int64_t donation,
        std::int64_t clawAmount,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "clawback drifted MPT claw " + std::to_string(clawAmount) + " (deposit=" +
            std::to_string(deposit) + ", donation=" + std::to_string(donation) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        mptt.authorize({.account = owner});
        env.close();
        env(pay(issuer, holder, asset(deposit)));
        env(pay(issuer, owner, asset(donation)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = asset(deposit)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(Vault::deposit(
                {.depositor = owner,
                 .id = vaultKeylet.key,
                 .amount = asset(donation),
                 .flags = tfVaultDonate}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(clawAmount), expected);
    }

    // Force an extreme vault state a real clawback cannot reach, then clawback the asset.
    void
    testUpdatedStateClawback(
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        std::int64_t clawAmount,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "clawback updated-state amount=" + std::to_string(clawAmount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", assetsAvailable=" + to_string(assetsAvailable) +
            ", sharesTotal=" + std::to_string(sharesTotal) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(1'000)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsAvailable, sharesTotal));
        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(clawAmount), expected);
    }

    // canBurnShares preclaim
    void
    compareCanBurnShares(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& owner,
        jtx::Account const& holder,
        Asset const& asset,
        TER expected)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        LeanCanBurnResult const lean = leanCanBurnShares(state);
        BEAST_EXPECTS(!lean.threw, "lean canBurnShares raised");

        env(Vault::clawback({.issuer = owner, .id = vaultKeylet.key, .holder = holder}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        std::optional<TER> const expectedError =
            expected == tesSUCCESS ? std::nullopt : std::optional<TER>{expected};
        BEAST_EXPECTS(
            (cppTer == tecNO_PERMISSION) == expectedError.has_value(),
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            lean.error == expectedError,
            std::string("error lean=") + (lean.error ? transToken(*lean.error) : "none") +
                " expected " + (expectedError ? transToken(*expectedError) : "none"));
    }

    void
    testCanBurnShares(
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "canBurnShares total=" + to_string(assetsTotal) +
            " avail=" + to_string(assetsAvailable) + " shares=" + std::to_string(sharesTotal));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsAvailable, sharesTotal));
        compareCanBurnShares(env, vaultKeylet, owner, holder, asset.raw(), expected);
    }

    // Vault.burnShares models the owner burning a holder's shares
    void
    testBurnShares(std::int64_t deposit, std::uint64_t stagedOutstanding)
    {
        using namespace jtx;
        testcase(
            "burnShares held=" + std::to_string(deposit) +
            " outstanding=" + std::to_string(stagedOutstanding));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(deposit)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = asset(deposit)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        // Empty the vault of assets (staged) so the owner may burn the remaining shares.
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{0}, Number{0}, stagedOutstanding));

        // The holder's actual share balance is what C++ burns and what the model is given.
        auto const shareMptId = env.le(vaultKeylet)->at(sfShareMPTID);
        std::int64_t const held =
            static_cast<std::int64_t>(env.le(keylet::mptoken(shareMptId, holder))->at(sfMPTAmount));
        VaultState const state = readVaultState(env, vaultKeylet, asset.raw());
        LeanBurnResult const burn =
            leanBurnShares(state, STAmount{shareIssue(env, vaultKeylet), held});

        env(Vault::clawback({.issuer = owner, .id = vaultKeylet.key, .holder = holder}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        auto const newVaultSle = env.le(vaultKeylet);
        Number const cppAssetsTotal = newVaultSle->at(sfAssetsTotal);
        Number const cppAssetsAvailable = newVaultSle->at(sfAssetsAvailable);
        Number const cppSharesTotal{static_cast<std::int64_t>(
            env.le(keylet::mptIssuance(shareMptId))->at(sfOutstandingAmount))};
        env.close();

        BEAST_EXPECTS(cppTer == tesSUCCESS, std::string("cpp=") + transToken(cppTer));
        BEAST_EXPECTS(!burn.threw, "lean burnShares raised");
        BEAST_EXPECTS(
            burn.vault.sharesTotal == cppSharesTotal,
            "sharesTotal lean=" + to_string(burn.vault.sharesTotal) +
                " cpp=" + to_string(cppSharesTotal));
        BEAST_EXPECT(burn.vault.assetsTotal == cppAssetsTotal);
        BEAST_EXPECT(burn.vault.assetsAvailable == cppAssetsAvailable);
    }

    // Discrepancy (C++ bug): on a 5:3 NAV-drifted vault, clawing 2 assets burns 1 share worth
    // 1.667, and C++ recovers round(1.667) = 2 assets while the model recovers 1 (rounds down).
    void
    testClawbackOvervaluedShares()
    {
        testClawbackDrifted(3, 2, 2, tesSUCCESS);
    }

    // Discrepancy (C++ bug): a clawback too small to debit assetsTotal (the debit rounds back
    // to the old value) still pays the issuer and burns the holder's shares. Same finding as
    // testWithdrawPrecisionLoss in LeanVaultWithdraw_test.cpp, the model rejects with
    // tecPRECISION_LOSS.
    void
    testClawbackPrecisionLoss()
    {
        using namespace jtx;
        testcase("clawback below assetsTotal precision");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(holder, asset(20'000'000'000)));
        env.close();
        env(pay(issuer, holder, asset(11'000'000'000)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        // Move assetsTotal to ~1e10 (ULP 1e-5): deposit 9,999,999,999.999999, then 0.00001.
        env(Vault::deposit(
                {.depositor = holder,
                 .id = vaultKeylet.key,
                 .amount = asset(Number{9'999'999'999'999'999LL, -6})}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(Number{1, -5})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // Clawback 1e-6, below the vault's 1e-5 ULP: the recovery cannot debit assetsTotal.
        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(Number{1, -6}), tecPRECISION_LOSS);
    }

    void
    runTests() override
    {
        using namespace jtx;

        Number const iouMax{9'999'999'999'999'999LL, 80};

        // Asset clawback by the issuer: partial, full, and over-seed (clamped to available).
        testClawbackAsset(1'000, 400, tesSUCCESS);
        testClawbackAsset(1'000, 1'000, tesSUCCESS);
        testClawbackAsset(1'000, 1'001, tesSUCCESS);

        // canBurnShares: every (assetsTotal, assetsAvailable, sharesTotal) combination
        testCanBurnShares(Number{0}, Number{0}, 0, tecNO_PERMISSION);
        testCanBurnShares(Number{0}, Number{0}, 1'000, tesSUCCESS);
        testCanBurnShares(Number{1'000}, Number{0}, 0, tecNO_PERMISSION);
        testCanBurnShares(Number{1'000}, Number{0}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(Number{1'000}, Number{1'000}, 0, tecNO_PERMISSION);
        testCanBurnShares(Number{1'000}, Number{1'000}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(Number{0}, Number{0}, kMaxMpTokenAmount, tesSUCCESS);
        // Per-field extremes: huge assets deny
        testCanBurnShares(iouMax, iouMax, 1'000, tecNO_PERMISSION);
        testCanBurnShares(iouMax, Number{0}, 1'000, tecNO_PERMISSION);
        testCanBurnShares(Number{0}, Number{0}, UINT64_MAX, tesSUCCESS);

        // Vault.burnShares
        testBurnShares(1'000'000'000, 1'000'000'000);
        testBurnShares(1'000'000'000, 2'000'000'000);
        testBurnShares(kMaxMpTokenAmount, kMaxMpTokenAmount);
        testBurnShares(1, kMaxMpTokenAmount);
        testBurnShares(1, 1);

        testClawbackAsset(kMaxMpTokenAmount, kMaxMpTokenAmount, tesSUCCESS);
        testClawbackAsset(kMaxMpTokenAmount, kMaxMpTokenAmount / 2, tesSUCCESS);
        testClawbackAsset(kMaxMpTokenAmount, 1, tesSUCCESS);
        testClawbackAsset(1, 1, tesSUCCESS);

        testClawbackAsset(1'000, 0, tecPRECISION_LOSS);

        // NAV-drifted vault (owner donation)
        testClawbackDrifted(3, 2, 3, tesSUCCESS);
        testClawbackDrifted(7, 5, 4, tesSUCCESS);

        testUpdatedStateClawback(iouMax, iouMax, 1'000, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(iouMax, iouMax, kMaxMpTokenAmount, 1, tecPRECISION_LOSS);
        testUpdatedStateClawback(Number{1'000}, Number{0}, 1'000, 400, tecPRECISION_LOSS);

        // Known discrepancies: each fails until the C++ code is fixed
        // testClawbackOvervaluedShares();  // model rounds down, C++ over-recovers
        // testClawbackPrecisionLoss();  // model tecPRECISION_LOSS, C++ pays without debiting
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClawback, formal_verification, xrpl);

}  // namespace xrpl::test
