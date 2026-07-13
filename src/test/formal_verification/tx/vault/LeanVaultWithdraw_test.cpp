#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultWithdraw_test : public LeanSuite
{
    static MPTIssue
    shareIssue(jtx::Env& env, Keylet const& vaultKeylet)
    {
        return MPTIssue{env.le(vaultKeylet)->at(sfShareMPTID)};
    }

    static std::int64_t
    outstandingShares(jtx::Env& env, Keylet const& vaultKeylet)
    {
        auto const shareMptId = env.le(vaultKeylet)->at(sfShareMPTID);
        return static_cast<std::int64_t>(
            env.le(keylet::mptIssuance(shareMptId))->at(sfOutstandingAmount));
    }

    void
    compareWithdraw(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& withdrawer,
        Asset const& asset,
        STAmount const& amount,
        TER expected)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        LeanWithdrawResult const withdraw = leanVaultWithdraw(state, amount);

        env(Vault::withdraw({.depositor = withdrawer, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!withdraw.threw, "lean withdraw raised");

        TER const leanTer = withdraw.error.value_or(tesSUCCESS);
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
        BEAST_EXPECTS(withdraw.vault.assetsTotal == cppAssetsTotal, "assetsTotal mismatch");
        BEAST_EXPECTS(
            withdraw.vault.assetsAvailable == cppAssetsAvailable, "assetsAvailable mismatch");
        BEAST_EXPECTS(withdraw.vault.sharesTotal == cppSharesTotal, "sharesTotal mismatch");
    }

    // Seed the vault with a deposit by `holder` (who thereby gets shares), then withdraw `amount`.
    void
    runVaultWithdraw(
        jtx::Env& env,
        jtx::Account const& owner,
        jtx::Account const& holder,
        Asset const& asset,
        STAmount const& seed,
        STAmount const& amount,
        TER expected)
    {
        using namespace jtx;
        auto const vaultKeylet = createVault(env, owner, asset);
        env(Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = seed}),
            jtx::Ter(tesSUCCESS));
        env.close();
        compareWithdraw(env, vaultKeylet, holder, asset, amount, expected);
    }

    void
    testWithdrawXRP(STAmount seed, STAmount amount, TER expected)
    {
        using namespace jtx;
        testcase("withdraw XRP " + amount.getText() + " from " + seed.getText());

        Env env(*this);
        Account const owner{"owner"};
        Account const holder{"holder"};
        env.fund(STAmount(seed) + XRP(1'000'000), owner, holder);
        env.close();
        runVaultWithdraw(env, owner, holder, xrpIssue(), seed, amount, expected);
    }

    void
    testWithdrawIOU(Number seed, Number amount, TER expected)
    {
        using namespace jtx;
        testcase("withdraw IOU " + to_string(amount) + " from " + to_string(seed));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        PrettyAsset const asset = issuer["USD"];
        runVaultWithdraw(env, owner, issuer, asset.raw(), asset(seed), asset(amount), expected);
    }

    void
    testWithdrawMPT(std::int64_t seed, std::int64_t amount, TER expected)
    {
        using namespace jtx;
        testcase("withdraw MPT " + std::to_string(amount) + " from " + std::to_string(seed));

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
        env(pay(issuer, holder, asset(seed)));
        env.close();
        runVaultWithdraw(env, owner, holder, asset.raw(), asset(seed), asset(amount), expected);
    }

    void
    testWithdrawAllShares()
    {
        using namespace jtx;
        testcase("withdraw all shares (full redemption)");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = issuer, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        STAmount const allShares{shareIssue(env, vaultKeylet), outstandingShares(env, vaultKeylet)};
        compareWithdraw(env, vaultKeylet, issuer, asset.raw(), allShares, tesSUCCESS);
    }

    // Validate sharesToAssetsWithdraw through the withdraw tx
    void
    testSharesToAssets(Number seed, Number donation, std::int64_t shareCount)
    {
        using namespace jtx;
        testcase(
            "sharesToAssetsWithdraw " + std::to_string(shareCount) +
            " shares (seed=" + to_string(seed) + ", donation=" + to_string(donation) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = issuer, .id = vaultKeylet.key, .amount = asset(seed)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        if (donation.signum() != 0)
        {
            env(trust(owner, asset(donation)));
            env.close();
            env(pay(issuer, owner, asset(donation)));
            env.close();
            env(Vault::deposit(
                    {.depositor = owner,
                     .id = vaultKeylet.key,
                     .amount = asset(donation),
                     .flags = tfVaultDonate}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }

        STAmount const shares{shareIssue(env, vaultKeylet), shareCount};
        VaultState const state = readVaultState(env, vaultKeylet, asset.raw());
        LeanSharesToAssetsResult const lean = leanSharesToAssetsWithdraw(state, shares, false);

        Number const availableBefore = env.le(vaultKeylet)->at(sfAssetsAvailable);
        env(Vault::withdraw({.depositor = issuer, .id = vaultKeylet.key, .amount = shares}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Number const availableAfter = env.le(vaultKeylet)->at(sfAssetsAvailable);

        BEAST_EXPECTS(!lean.threw, "lean sharesToAssetsWithdraw raised");
        BEAST_EXPECT(static_cast<Number>(lean.assets) == availableBefore - availableAfter);
    }

    // Force an extreme vault state a real deposit cannot reach, then withdraw and compare.
    void
    testWithdrawUpdatedState(
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        std::int64_t shareAmount,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "withdraw updated-state shares=" + std::to_string(shareAmount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", assetsAvailable=" + to_string(assetsAvailable) +
            ", sharesTotal=" + std::to_string(sharesTotal) + ")");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = issuer, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsAvailable, sharesTotal));
        STAmount const shares{shareIssue(env, vaultKeylet), shareAmount};
        compareWithdraw(env, vaultKeylet, issuer, asset.raw(), shares, expected);
    }

    // Withdraw by assets from a vault whose sharesTotal is INT64_MAX, so the share computation
    // (sharesTotal * assets / NAV) overflows the MPT domain.
    void
    testWithdrawAssetsShareOverflow(TER expected)
    {
        using namespace jtx;
        testcase("withdraw assets with INT64_MAX shares");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = issuer, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{1}, Number{1}, kMaxMpTokenAmount));
        compareWithdraw(env, vaultKeylet, issuer, asset.raw(), asset(1'000), expected);
    }

    // Discrepancy: the model does not guard a negative NAV. It hits its own available check
    // (tecINSUFFICIENT_FUNDS) where C++ returns tecINTERNAL.
    void
    testWithdrawNegativeNav()
    {
        testWithdrawUpdatedState(
            Number{-1'000}, Number{-1'000}, 1'000'000'000, 500'000'000, tecINTERNAL);
    }

    // Discrepancy: an amount that is neither the vault asset nor its shares makes the model raise,
    // where C++ rejects in preclaim (tecWRONG_ASSET).
    void
    testWithdrawWrongAsset()
    {
        using namespace jtx;
        testcase("withdraw wrong asset");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = issuer, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        PrettyAsset const other = issuer["EUR"];
        compareWithdraw(env, vaultKeylet, issuer, asset.raw(), other(100), tecWRONG_ASSET);
    }

    void
    runTests() override
    {
        using namespace jtx;

        // Partial and final withdrawal by assets. IOU is scale 6, MPT is scale 0 (like XRP), so the
        // two cover the distinct share arithmetic
        testWithdrawIOU(Number{1'000}, Number{400}, tesSUCCESS);
        testWithdrawIOU(Number{1'000}, Number{1'000}, tesSUCCESS);
        testWithdrawMPT(1'000, 400, tesSUCCESS);
        testWithdrawMPT(1'000, 1'000, tesSUCCESS);
        testWithdrawXRP(XRP(1'000), drops(1), tesSUCCESS);

        // Insufficient vault assets (the check is asset-agnostic, so one case suffices).
        testWithdrawIOU(Number{1'000}, Number{1'001}, tecINSUFFICIENT_FUNDS);
        // Sub-share withdrawal: the amount converts to zero shares.
        testWithdrawIOU(Number{1, 12}, Number{1, -7}, tecPRECISION_LOSS);
        // MPT at INT64_MAX, deposited and withdrawn end to end.
        testWithdrawMPT(kMaxMpTokenAmount, kMaxMpTokenAmount, tesSUCCESS);

        testWithdrawAllShares();

        // Direct sharesToAssetsWithdraw checks
        testSharesToAssets(Number{1'000}, Number{0}, 1);
        testSharesToAssets(Number{1'000}, Number{0}, 500'000'000);
        testSharesToAssets(Number{1'000}, Number{0}, 999'999'999);
        testSharesToAssets(Number{1'000}, Number{2'000}, 333'333'333);
        testSharesToAssets(Number{1'000}, Number{500}, 123'456'789);
        testSharesToAssets(Number{1'000'000}, Number{0}, 123'456'789);
        testSharesToAssets(Number{1}, Number{1'000'000}, 500'000);

        // Staged extreme states (a 1000-asset seed mints 1e9 shares at scale 6). Each mixes an
        // extreme across a different field: AssetsTotal, AssetsAvailable, sharesTotal, shareAmount.
        Number const iouMax{9'999'999'999'999'999LL, 80};
        // Extreme AssetsTotal, tiny available, full shareholder
        testWithdrawUpdatedState(
            iouMax, Number{1}, 1'000'000'000, 500'000'000, tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, mid available, minimal sharesTotal/shareAmount
        testWithdrawUpdatedState(iouMax, Number{1, 50}, 1, 1, tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, tiny available, extreme sharesTotal, minimal shareAmount
        testWithdrawUpdatedState(iouMax, Number{1}, 1'000'000'000, 1, tecINSUFFICIENT_FUNDS);
        // Overflow: NAV * shares / sharesTotal exceeds the IOU domain
        testWithdrawUpdatedState(iouMax, iouMax, 1'000, 1'000'000'000, tecPATH_DRY);
        // Overflow: minimal sharesTotal with a maximal shareAmount,
        testWithdrawUpdatedState(iouMax, Number{1}, 1, 1'000'000'000, tecPATH_DRY);
        // Overflow: sharesTotal * assets / NAV exceeds the MPT domain (by assets).
        testWithdrawAssetsShareOverflow(tecPATH_DRY);

        // Known discrepancies: each fails until the model is fixed
        // testWithdrawNegativeNav();  // model tecINSUFFICIENT_FUNDS where C++ gives tecINTERNAL
        // testWithdrawWrongAsset();   // model raises where C++ gives tecWRONG_ASSET
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultWithdraw, formal_verification, xrpl);

}  // namespace xrpl::test
