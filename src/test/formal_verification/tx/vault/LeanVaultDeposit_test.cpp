#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/deposit.h>
#include <test/formal_verification/ffi/vault/state.h>
#include <test/jtx.h>
#include <test/jtx/ter.h>

#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <limits>
#include <optional>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultDeposit_test : public LeanSuite
{
    static Keylet
    createVault(jtx::Env& env, jtx::Account const& owner, Asset const& asset)
    {
        jtx::Vault vault{env};
        auto const [jv, keylet] = vault.create({.owner = owner, .asset = asset});
        env(jv);
        env.close();
        return keylet;
    }

    // Create a vault, optionally seed it (a first deposit by `seeder`), then deposit `amount` as
    // `depositor` and compare the model against C++
    void
    runDeposit(
        jtx::Env& env,
        jtx::Account const& vaultOwner,
        jtx::Account const& seeder,
        jtx::Account const& depositor,
        Asset const& asset,
        STAmount const& vaultBalanceBeforeDeposit,
        STAmount const& amount,
        TER cppExpected,
        TER leanExpected,
        STAmount const& donation = STAmount{})
    {
        using namespace jtx;
        auto const vaultKeylet = createVault(env, vaultOwner, asset);

        if (vaultBalanceBeforeDeposit.signum() != 0)
        {
            env(Vault::deposit(
                    {.depositor = seeder,
                     .id = vaultKeylet.key,
                     .amount = vaultBalanceBeforeDeposit}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }

        // An owner donation adds assets with no shares, drifting NAV off shareTotal/10^scale so the
        // exchange-rate path is exercised with a non-terminating ratio.
        if (donation.signum() != 0)
        {
            env(Vault::deposit(
                    {.depositor = vaultOwner,
                     .id = vaultKeylet.key,
                     .amount = donation,
                     .flags = tfVaultDonate}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }

        auto const vaultSle = env.le(vaultKeylet);
        auto const shareMptId = vaultSle->at(sfShareMPTID);
        auto const issuanceKeylet = keylet::mptIssuance(shareMptId);
        VaultState const state{
            .assetsTotal = vaultSle->at(sfAssetsTotal),
            .assetsAvailable = vaultSle->at(sfAssetsAvailable),
            .asset = asset,
            .scale = vaultSle->at(sfScale),
            .sharesTotal =
                Number{static_cast<std::int64_t>(env.le(issuanceKeylet)->at(sfOutstandingAmount))},
            .sharesAsset = MPTIssue{shareMptId},
            .interestUnrealized = vaultSle->at(sfInterestUnrealized),
            .lossUnrealized = vaultSle->at(sfLossUnrealized)};

        LeanRoundedDepositAmountResult const rounded = leanRoundedDepositAmount(state, amount);
        LeanDepositResult const deposit = leanVaultDeposit(state, amount, false);
        BEAST_EXPECTS(!rounded.threw, "lean roundedDepositAmount raised");

        env(Vault::deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        // The lean TER is the first error surfaced: roundedDepositAmount's rejection, else the full
        // deposit's error. cppExpected/leanExpected differ only for a documented model gap.
        TER leanTer = tesSUCCESS;
        if (rounded.error)
        {
            leanTer = *rounded.error;
        }
        else if (!deposit.threw && deposit.error)
        {
            leanTer = *deposit.error;
        }
        BEAST_EXPECTS(
            cppTer == cppExpected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(cppExpected));
        BEAST_EXPECTS(
            leanTer == leanExpected,
            std::string("lean=") + transToken(leanTer) + " expected " + transToken(leanExpected));

        if (cppTer != tesSUCCESS)
            return;

        // On success the model must have completed and its new vault state must match the env: the
        // updated assetsTotal (checks rounding parity) and sharesTotal == the share MPT
        // outstanding.
        BEAST_EXPECTS(!deposit.threw, "lean deposit raised on success");
        auto const newVaultSle = env.le(vaultKeylet);
        Number const cppAssetsTotal = newVaultSle->at(sfAssetsTotal);
        Number const cppAssetsAvailable = newVaultSle->at(sfAssetsAvailable);
        Number const cppSharesTotal{
            static_cast<std::int64_t>(env.le(issuanceKeylet)->at(sfOutstandingAmount))};
        BEAST_EXPECTS(deposit.newState.assetsTotal == cppAssetsTotal, "assetsTotal mismatch");
        BEAST_EXPECTS(
            deposit.newState.assetsAvailable == cppAssetsAvailable, "assetsAvailable mismatch");
        BEAST_EXPECTS(deposit.newState.sharesTotal == cppSharesTotal, "sharesTotal mismatch");
    }

    void
    testDepositXRP(STAmount vaultBalanceBeforeDeposit, STAmount amount, TER expected)
    {
        using namespace jtx;
        testcase(
            "deposit XRP " + amount.getText() + " into " + vaultBalanceBeforeDeposit.getText());

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const holder{"holder"};
        env.fund(STAmount(vaultBalanceBeforeDeposit) + XRP(1'000'000), vaultOwner);
        env.fund(STAmount(amount) + XRP(1'000'000), holder);
        env.close();

        runDeposit(
            env,
            vaultOwner,
            vaultOwner,
            holder,
            xrpIssue(),
            vaultBalanceBeforeDeposit,
            amount,
            expected,
            expected);
    }

    void
    testDepositIOU(
        Number vaultBalanceBeforeDeposit,
        Number amount,
        bool depositorIsIssuer,
        TER expected,
        std::optional<TER> leanExpected = std::nullopt)
    {
        using namespace jtx;
        testcase(
            "deposit IOU " + to_string(amount) + " into " + to_string(vaultBalanceBeforeDeposit) +
            (depositorIsIssuer ? " (issuer)" : ""));

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), vaultOwner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        Account const depositor = depositorIsIssuer ? issuer : holder;
        if (!depositorIsIssuer)
        {
            // limit large enough to cover any tested amount
            env(trust(holder, asset(10'000'000'000'000'000LL)));
            env.close();
            env(pay(issuer, holder, asset(amount)));
            env.close();
        }

        // The issuer seeds the vault (it can issue any amount of its own IOU). leanExpected
        // defaults to the cpp expectation (a true match) unless a divergence is passed.
        runDeposit(
            env,
            vaultOwner,
            issuer,
            depositor,
            asset.raw(),
            asset(vaultBalanceBeforeDeposit),
            asset(amount),
            expected,
            leanExpected.value_or(expected));
    }

    void
    testDepositMPT(std::int64_t vaultBalanceBeforeDeposit, std::int64_t amount, TER expected)
    {
        using namespace jtx;
        testcase(
            "deposit MPT " + std::to_string(amount) + " into " +
            std::to_string(vaultBalanceBeforeDeposit));

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), vaultOwner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(amount)));
        env.close();

        runDeposit(
            env,
            vaultOwner,
            issuer,
            holder,
            asset.raw(),
            asset(vaultBalanceBeforeDeposit),
            asset(amount),
            expected,
            expected);
    }

    // Exchange-rate path with NAV drifted off shareTotal/10^scale by an owner donation, so the
    // shares come from a genuine non-terminating division (NAV = seed + donation). Guards the
    // non-empty assetsToShares / sharesToAssets arithmetic.
    void
    testDepositExchangeRate()
    {
        using namespace jtx;
        testcase("deposit exchange rate (NAV-drifted vault)");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), vaultOwner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        // The owner must hold the asset to donate it.
        env(trust(vaultOwner, asset(1'000'000)));
        env.close();
        env(pay(issuer, vaultOwner, asset(1'000)));
        env.close();

        // Seed 1 + donate 2 -> NAV 3, shareTotal 1e6 (ratio 1e6/3); deposit 100 -> 33'333'333
        // shares.
        runDeposit(
            env,
            vaultOwner,
            issuer,
            issuer,
            asset.raw(),
            asset(Number{1}),
            asset(Number{100}),
            tesSUCCESS,
            tesSUCCESS,
            asset(Number{2}));
    }

    // Documented, out-of-scope divergence: a non-issuer deposit whose amount rounds to zero at the
    // depositor's own trust-line scale is rejected by C++ (preclaim, VaultDeposit.cpp:205-217) but
    // out of scope of the model.
    void
    testDepositTrustLineScale()
    {
        using namespace jtx;
        testcase("deposit below depositor trust-line scale (documented divergence)");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), vaultOwner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        // A large holder balance gives a coarse trust-line scale (ULP ~ 1e-3), so a 1e-6 deposit
        // vanishes at that scale.
        env(trust(holder, asset(1'000'000'000'000'000LL)));
        env.close();
        env(pay(issuer, holder, asset(Number{1, 12})));
        env.close();

        // 1e-6 USD: C++ rounds it to zero at the holder's ~1e-3 balance scale -> tecPRECISION_LOSS.
        // The model computes shares = truncate(1e-6 * 1e6) = 1 and succeeds. cppExpected != lean.
        runDeposit(
            env,
            vaultOwner,
            issuer,  // seeder (unused: fresh vault)
            holder,  // non-issuer depositor
            asset.raw(),
            asset(Number{0}),  // fresh vault
            asset(Number{1, -6}),
            tecPRECISION_LOSS,  // cpp
            tesSUCCESS);        // lean (documented divergence)
    }

    void
    testDepositScenarios()
    {
        using namespace jtx;

        // XRP: scale 0, no share overflow within the XRP domain.
        testDepositXRP(XRP(0), drops(1), tesSUCCESS);
        testDepositXRP(XRP(0), XRP(1'000), tesSUCCESS);
        testDepositXRP(XRP(0), XRP(80'000'000'000), tesSUCCESS);
        testDepositXRP(XRP(1'000), XRP(1'000), tesSUCCESS);  // non-empty vault

        // IOU: default vault scale 6, so shares ~ amount * 1e6; overflow above kMaxMptTokenAmount /
        // 1e6.
        testDepositIOU(Number{0}, Number{1}, false, tesSUCCESS);
        testDepositIOU(Number{0}, Number{1'000}, false, tesSUCCESS);
        testDepositIOU(Number{0}, Number{kMaxMpTokenAmount / 1'000'000}, false, tesSUCCESS);
        // Over the share ceiling: C++ overflows in doApply -> tecPATH_DRY, but the preclaim model
        // (roundedDepositAmount) does not cover that and returns tesSUCCESS. Documented gap:
        // cppExpected = tecPATH_DRY, leanExpected = tesSUCCESS.
        testDepositIOU(
            Number{0}, Number{(kMaxMpTokenAmount / 1'000'000) + 1}, false, tecPATH_DRY, tesSUCCESS);

        testDepositIOU(Number{0}, Number{1}, true, tesSUCCESS);
        testDepositIOU(Number{0}, Number{kMaxMpTokenAmount / 1'000'000}, true, tesSUCCESS);
        testDepositIOU(
            Number{0}, Number{(kMaxMpTokenAmount / 1'000'000) + 1}, true, tecPATH_DRY, tesSUCCESS);

        // Precision loss: a sub-ULP deposit into a large vault rounds to zero at the vault scale.
        // Vault holds 1e12 USD -> ULP 1e-3; depositing 1e-4 rounds to zero -> tecPRECISION_LOSS.
        testDepositIOU(Number{1, 12}, Number{1, -4}, false, tecPRECISION_LOSS);
        testDepositIOU(Number{1, 12}, Number{1, -4}, true, tecPRECISION_LOSS);
        // sanity: a normal deposit into the same non-empty vault still succeeds
        testDepositIOU(Number{1, 12}, Number{1'000}, false, tesSUCCESS);

        // MPT: scale 0; max deposit is the MPT ceiling itself.
        testDepositMPT(0, 1, tesSUCCESS);
        testDepositMPT(0, 1'000, tesSUCCESS);
        testDepositMPT(0, kMaxMpTokenAmount, tesSUCCESS);

        // Rounding-mode regression traps, these values catch potential rounding mode changes
        testDepositIOU(Number{1, 12}, Number{100006, -4}, false, tesSUCCESS);
        testDepositIOU(Number{1, 12}, Number{100001, -4}, false, tesSUCCESS);

        // Empty-vault share truncation (C++ truncates toward zero, not to-nearest):
        // 1.5e-6 USD * 1e6 scale = 1.5 shares -> 1.
        testDepositIOU(Number{0}, Number{15, -7}, true, tesSUCCESS);
        // Zero-share deposit is rejected: 0.6e-6 USD * 1e6 = 0.6 shares -> 0 -> tecPRECISION_LOSS.
        testDepositIOU(Number{0}, Number{6, -7}, true, tecPRECISION_LOSS);

        // Exchange-rate path with a drifted NAV (non-terminating share division).
        testDepositExchangeRate();

        // The precision tests above deposit as the issuer (for whom the depositor trust-line-scale
        // check is skipped) to isolate the vault arithmetic. testDepositTrustLineScale documents
        // the non-issuer divergence (out of scope: it depends on the depositor's balance, not the
        // vault).
        testDepositTrustLineScale();
    }

    void
    runTests() override
    {
        testDepositScenarios();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test
