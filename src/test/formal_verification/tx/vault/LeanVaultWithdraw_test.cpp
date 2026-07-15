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
        TER expected,
        bool waiveUnrealizedLoss = false)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        bool const byShares = amount.asset() != asset;
        LeanWithdrawResult const withdraw =
            leanVaultWithdraw(state, amount, byShares, waiveUnrealizedLoss);

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
        BEAST_EXPECTS(
            withdraw.vault.assetsTotal == cppAssetsTotal,
            "assetsTotal lean=" + to_string(withdraw.vault.assetsTotal) +
                " cpp=" + to_string(cppAssetsTotal));
        BEAST_EXPECTS(
            withdraw.vault.assetsAvailable == cppAssetsAvailable,
            "assetsAvailable lean=" + to_string(withdraw.vault.assetsAvailable) +
                " cpp=" + to_string(cppAssetsAvailable));
        BEAST_EXPECTS(
            withdraw.vault.sharesTotal == cppSharesTotal,
            "sharesTotal lean=" + to_string(withdraw.vault.sharesTotal) +
                " cpp=" + to_string(cppSharesTotal));
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

    // Finding (C++ bug): a share withdrawal pays round-to-nearest, so a single-share withdraw from
    // a vault pays more than the share is worth.
    void
    testWithdrawOvervaluedShares()
    {
        using namespace jtx;
        testcase("withdraw overvalued shares");

        Env env(*this);
        Account const owner{"owner"};
        Account const bob{"bob"};
        env.fund(XRP(1'000'000), owner, bob);
        env.close();

        auto const vaultKeylet = createVault(env, owner, xrpIssue());
        // bob deposits 3 drops (3 shares) and the owner donates 2 drops, so 3 shares now back
        // 5 drops (1 share = 1.667 drops). A single-share withdraw pays round(1.667) = 2 in C++,
        // 1 in model.
        env(Vault::deposit({.depositor = bob, .id = vaultKeylet.key, .amount = drops(3)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(Vault::deposit(
                {.depositor = owner,
                 .id = vaultKeylet.key,
                 .amount = drops(2),
                 .flags = tfVaultDonate}),
            jtx::Ter(tesSUCCESS));
        env.close();

        STAmount const oneShare{shareIssue(env, vaultKeylet), 1};
        compareWithdraw(env, vaultKeylet, bob, xrpIssue(), oneShare, tesSUCCESS);
    }

    // Finding (C++ bug): a withdrawal too small to debit assetsTotal (the debit rounds back to the
    // old value) still pays the withdrawer. C++ only catches it with the global invariant, where
    // it should reject with tecPRECISION_LOSS.
    void
    testWithdrawPrecisionLoss()
    {
        using namespace jtx;
        testcase("withdraw below assetsTotal precision");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        // Move assetsTotal to ~1e10 (ULP 1e-5): deposit 9,999,999,999.999999, then 0.00001.
        env(Vault::deposit(
                {.depositor = issuer,
                 .id = vaultKeylet.key,
                 .amount = asset(Number{9'999'999'999'999'999LL, -6})}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(Vault::deposit(
                {.depositor = issuer, .id = vaultKeylet.key, .amount = asset(Number{1, -5})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // Withdraw 1e-6, below the vault's 1e-5 ULP: the payout cannot debit assetsTotal.
        compareWithdraw(
            env, vaultKeylet, issuer, asset.raw(), asset(Number{1, -6}), tecPRECISION_LOSS);
    }

    // Finding (C++ bug): preclaim computes waiveUnrealizedLoss (Yes for a sole shareholder) but
    // doApply ignores it and applies the loss, paying the withdrawer less.
    void
    testWithdrawWaiveLoss()
    {
        using namespace jtx;
        testcase("withdraw sole shareholder waives unrealized loss");

        Env env(*this);
        Account const issuer{"issuer"};
        Account const lender{"lender"};
        Account const borrower{"borrower"};
        env.fund(XRP(1'000'000), issuer, lender, borrower);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(lender, asset(10'000'000)));
        env(trust(borrower, asset(10'000'000)));
        env.close();
        env(pay(issuer, lender, asset(1'000'000)));
        env(pay(issuer, borrower, asset(100'000)));
        env.close();

        // The lender is the sole shareholder.
        auto const vaultKeylet = createVault(env, lender, asset.raw());
        env(Vault::deposit({.depositor = lender, .id = vaultKeylet.key, .amount = asset(5'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // A loan impaired immediately gives the vault a real unrealized loss.
        auto const brokerID = keylet::loanbroker(lender.id(), env.seq(lender)).key;
        {
            using namespace loanBroker;
            env(set(lender, vaultKeylet.key), kDebtMaximum(asset(33'330).value()));
            env.close();
        }
        auto const sleBroker = env.le(keylet::loanbroker(brokerID));
        BEAST_EXPECT(sleBroker);
        auto const loanKeylet = keylet::loan(brokerID, sleBroker->at(sfLoanSequence));
        {
            using namespace loan;
            env(set(borrower, brokerID, 3'333),
                Sig(sfCounterpartySignature, lender),
                kPaymentTotal(2),
                kPaymentInterval(600),
                Fee(env.current()->fees().base * 2),
                jtx::Ter(tesSUCCESS));
            env.close();
            env(manage(lender, loanKeylet.key, tfLoanImpair), jtx::Ter(tesSUCCESS));
            env.close();
        }
        BEAST_EXPECT(env.le(vaultKeylet)->at(sfLossUnrealized) != Number{0});

        // Sole shareholder withdraws shares: model waives the loss (higher payout), C++ doApply
        // applies it (lower payout).
        STAmount const shares{shareIssue(env, vaultKeylet), 100'000'000};
        compareWithdraw(env, vaultKeylet, lender, asset.raw(), shares, tesSUCCESS, true);
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

        // Known discrepancies: each fails until the C++ code is fixed
        // testWithdrawOvervaluedShares();  // model rounds the payout down where C++ overpays
        // testWithdrawPrecisionLoss();  // model tecPRECISION_LOSS where C++ hits the invariant
        // testWithdrawWaiveLoss();  // model waives the loss where C++ applies it
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultWithdraw, formal_verification, xrpl);

}  // namespace xrpl::test
