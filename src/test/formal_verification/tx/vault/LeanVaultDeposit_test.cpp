#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultDeposit_test : public LeanSuite
{
    // Model of preclaim: leanRoundedDepositAmount rounds to the vault scale and returns exactly
    // one of the rounded amount (success) or an error TER.
    void
    compareRoundedDepositAmount(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& depositor,
        Asset const& asset,
        STAmount const& amount,
        TER expected)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        LeanRoundedDepositAmountResult const rounded = leanRoundedDepositAmount(state, amount);

        env(Vault::deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));

        std::optional<TER> const leanError =
            rounded.threw ? std::optional<TER>{tefEXCEPTION} : rounded.error;
        std::optional<TER> const expectedError =
            expected == tesSUCCESS ? std::nullopt : std::optional<TER>{expected};
        std::optional<STAmount> const expectedAmount =
            expected == tesSUCCESS ? std::optional<STAmount>{amount} : std::nullopt;
        BEAST_EXPECTS(
            leanError == expectedError,
            std::string("error lean=") + (leanError ? transToken(*leanError) : "none") +
                " expected " + (expectedError ? transToken(*expectedError) : "none"));
        BEAST_EXPECTS(
            rounded.amount == expectedAmount,
            std::string("amount lean=") + (rounded.amount ? rounded.amount->getText() : "none") +
                " expected " + (expectedAmount ? expectedAmount->getText() : "none"));
    }

    // Model of doApply: leanVaultDeposit computes shares and the new vault state.
    void
    compareVaultDeposit(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& depositor,
        Asset const& asset,
        STAmount const& amount,
        TER expected)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        LeanDepositResult const deposit = leanVaultDeposit(state, amount, false);

        env(Vault::deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));

        // A model raise surfaces as tefEXCEPTION, matching the C++ transactor.
        std::optional<TER> const leanError =
            deposit.threw ? std::optional<TER>{tefEXCEPTION} : deposit.error;
        std::optional<TER> const expectedError =
            expected == tesSUCCESS ? std::nullopt : std::optional<TER>{expected};
        BEAST_EXPECTS(
            leanError == expectedError,
            std::string("error lean=") + (leanError ? transToken(*leanError) : "none") +
                " expected " + (expectedError ? transToken(*expectedError) : "none"));

        if (cppTer != tesSUCCESS)
            return;

        auto const newVaultSle = env.le(vaultKeylet);
        auto const issuanceKeylet = keylet::mptIssuance(newVaultSle->at(sfShareMPTID));
        Number const cppAssetsTotal = newVaultSle->at(sfAssetsTotal);
        Number const cppAssetsAvailable = newVaultSle->at(sfAssetsAvailable);
        Number const cppSharesTotal{
            static_cast<std::int64_t>(env.le(issuanceKeylet)->at(sfOutstandingAmount))};
        BEAST_EXPECTS(
            deposit.vault.assetsTotal == cppAssetsTotal,
            "assetsTotal lean=" + to_string(deposit.vault.assetsTotal) +
                " cpp=" + to_string(cppAssetsTotal));
        BEAST_EXPECTS(
            deposit.vault.assetsAvailable == cppAssetsAvailable,
            "assetsAvailable lean=" + to_string(deposit.vault.assetsAvailable) +
                " cpp=" + to_string(cppAssetsAvailable));
        BEAST_EXPECTS(
            deposit.vault.sharesTotal == cppSharesTotal,
            "sharesTotal lean=" + to_string(deposit.vault.sharesTotal) +
                " cpp=" + to_string(cppSharesTotal));
    }

    void
    runVaultDeposit(
        jtx::Env& env,
        jtx::Account const& vaultOwner,
        jtx::Account const& seeder,
        jtx::Account const& depositor,
        Asset const& asset,
        STAmount const& vaultBalanceBeforeDeposit,
        STAmount const& amount,
        TER expected,
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

        // An owner donation adds assets without shares, drifting NAV off shareTotal/10^scale to
        // exercise the exchange-rate path.
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

        compareVaultDeposit(env, vaultKeylet, depositor, asset, amount, expected);
    }

    void
    testVaultDepositXRP(STAmount vaultBalanceBeforeDeposit, STAmount amount, TER expected)
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

        runVaultDeposit(
            env,
            vaultOwner,
            vaultOwner,
            holder,
            xrpIssue(),
            vaultBalanceBeforeDeposit,
            amount,
            expected);
    }

    void
    testVaultDepositIOU(
        Number vaultBalanceBeforeDeposit,
        Number amount,
        bool depositorIsIssuer,
        TER expected)
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

        // The issuer seeds the vault, since it can issue any amount of its own IOU.
        runVaultDeposit(
            env,
            vaultOwner,
            issuer,
            depositor,
            asset.raw(),
            asset(vaultBalanceBeforeDeposit),
            asset(amount),
            expected);
    }

    void
    testVaultDepositMPT(std::int64_t vaultBalanceBeforeDeposit, std::int64_t amount, TER expected)
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
        // The holder seeds and deposits, so it must hold both amounts (an MPT issuer cannot
        // deposit an MPToken it does not itself hold).
        env(pay(issuer, holder, asset(vaultBalanceBeforeDeposit + amount)));
        env.close();

        runVaultDeposit(
            env,
            vaultOwner,
            holder,
            holder,
            asset.raw(),
            asset(vaultBalanceBeforeDeposit),
            asset(amount),
            expected);
    }

    // Exchange-rate path: an owner donation drifts NAV so shares come from a non-terminating
    // division, exercising the non-empty assetsToShares / sharesToAssets arithmetic.
    void
    testVaultDepositExchangeRate()
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
        runVaultDeposit(
            env,
            vaultOwner,
            issuer,
            issuer,
            asset.raw(),
            asset(Number{1}),
            asset(Number{100}),
            tesSUCCESS,
            asset(Number{2}));
    }

    // Update an MPT vault to an extreme state a real deposit cannot reach, then deposit and
    // compare.
    void
    testVaultDepositUpdatedStateMPT(
        Number const& assetsTotal,
        std::uint64_t sharesTotal,
        std::int64_t amount,
        TER expected)
    {
        using namespace jtx;
        testcase(
            "updated-state MPT deposit " + std::to_string(amount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", sharesTotal=" + std::to_string(sharesTotal) + ")");

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

        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsTotal, sharesTotal));
        compareVaultDeposit(env, vaultKeylet, holder, asset.raw(), asset(amount), expected);
    }

    // Update an IOU vault to an extreme AssetsTotal so a small issuer deposit rounds to zero (or
    // overflows) at the vault scale.
    void
    testRoundedDepositUpdatedStateIOU(Number const& assetsTotal, Number const& amount, TER expected)
    {
        using namespace jtx;
        testcase(
            "updated-state IOU deposit " + to_string(amount) +
            " (assetsTotal=" + to_string(assetsTotal) + ")");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), vaultOwner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        // Update shares so the vault is not zero-sized, the deposit still rejects on rounding.
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, assetsTotal, assetsTotal, 1'000'000));
        compareRoundedDepositAmount(env, vaultKeylet, issuer, asset.raw(), asset(amount), expected);
    }

    // A normal deposit is already at the vault scale, so roundedDepositAmount returns it unchanged
    // with no error.
    void
    testRoundedDepositSuccess()
    {
        using namespace jtx;
        testcase("roundedDepositAmount at vault scale");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), vaultOwner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        env(Vault::deposit(
                {.depositor = issuer, .id = vaultKeylet.key, .amount = asset(Number{1, 12})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareRoundedDepositAmount(
            env, vaultKeylet, issuer, asset.raw(), asset(Number{1'000}), tesSUCCESS);
    }

    // Under ULP deposit into a non-empty vault: preclaim rounds it to zero at the vault scale
    void
    testRoundedDepositBelowVaultScale(bool depositorIsIssuer)
    {
        using namespace jtx;
        testcase(std::string("deposit below vault scale") + (depositorIsIssuer ? " (issuer)" : ""));

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
            env(trust(holder, asset(10'000'000'000'000'000LL)));
            env.close();
            env(pay(issuer, holder, asset(Number{1, -4})));
            env.close();
        }

        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        // Vault holds 1e12 USD -> ULP ~1e-3, so depositing 1e-4 rounds to zero at the vault scale.
        env(Vault::deposit(
                {.depositor = issuer, .id = vaultKeylet.key, .amount = asset(Number{1, 12})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareRoundedDepositAmount(
            env, vaultKeylet, depositor, asset.raw(), asset(Number{1, -4}), tecPRECISION_LOSS);
    }

    // Discrepancy (out of scope): a deposit that rounds to zero at the depositor's trust-line scale
    // is rejected by C++ (tecPRECISION_LOSS), but the model rounds only to the vault scale so
    // leanRoundedDepositAmount accepts it (no per-account balance in the model).
    void
    testRoundedDepositTrustLineScale()
    {
        using namespace jtx;
        testcase("deposit below depositor trust-line scale");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), vaultOwner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        // A large holder balance gives a coarse trust-line scale (ULP ~1e-3), so a 1e-6 deposit is
        // zero there but not at the empty vault's scale.
        env(trust(holder, asset(1'000'000'000'000'000LL)));
        env.close();
        env(pay(issuer, holder, asset(Number{1, 12})));
        env.close();

        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        compareRoundedDepositAmount(
            env, vaultKeylet, holder, asset.raw(), asset(Number{1, -6}), tecPRECISION_LOSS);
    }

    // Discrepancy: the model does not model the MPT mint ceiling. A deposit that would push
    // outstanding shares past INT64_MAX succeeds where C++ returns tecPATH_DRY.
    void
    testVaultDepositMptCeiling()
    {
        testVaultDepositUpdatedStateMPT(
            Number{static_cast<std::int64_t>(kMaxMpTokenAmount)},
            kMaxMpTokenAmount,
            1'000,
            tecPATH_DRY);
    }

    // AssetsTotal + amount near the IOU maximum overflows.
    void
    testRoundedDepositOverflow()
    {
        testRoundedDepositUpdatedStateIOU(
            Number{9'999'999'999'999'999LL, 80}, Number{9'999'999'999'999'999LL, 80}, tefEXCEPTION);
    }

    // Finding (C++ bug): a deposit charges round-to-nearest, so a deposit into a vault
    // can be undercharged, overvaluing the new shares and diluting existing holders.
    void
    testVaultDepositOvervaluedShares()
    {
        using namespace jtx;
        testcase("deposit overvalued shares");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const bob{"bob"};
        env.fund(XRP(1'000'000), vaultOwner, bob);
        env.close();

        auto const vaultKeylet = createVault(env, vaultOwner, xrpIssue());
        // The owner deposits 3 drops (3 shares) then donates 2 drops, so 3 shares now back 5 drops
        // (1 share = 1.667 drops). bob depositing 4 drops gets 2 shares. C++ charges round(3.33) =
        // 3, the model charges ceil = 4.
        env(Vault::deposit({.depositor = vaultOwner, .id = vaultKeylet.key, .amount = drops(3)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(Vault::deposit(
                {.depositor = vaultOwner,
                 .id = vaultKeylet.key,
                 .amount = drops(2),
                 .flags = tfVaultDonate}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareVaultDeposit(env, vaultKeylet, bob, xrpIssue(), drops(4), tesSUCCESS);
    }

    void
    runTests() override
    {
        using namespace jtx;

        // XRP: scale 0, no share overflow within the XRP domain.
        testVaultDepositXRP(XRP(0), drops(1), tesSUCCESS);  // minimum deposit
        testVaultDepositXRP(XRP(0), XRP(1'000), tesSUCCESS);
        testVaultDepositXRP(XRP(0), XRP(80'000'000'000), tesSUCCESS);
        testVaultDepositXRP(XRP(1'000), XRP(1'000), tesSUCCESS);  // non-empty vault
        testVaultDepositXRP(XRP(1'000), drops(1), tesSUCCESS);    // minimum deposit, non-empty

        // IOU: default vault scale 6, so shares ~ amount * 1e6; over kMaxMpTokenAmount / 1e6 the
        // share amount overflows.
        testVaultDepositIOU(Number{0}, Number{1}, false, tesSUCCESS);
        testVaultDepositIOU(Number{0}, Number{1'000}, false, tesSUCCESS);
        testVaultDepositIOU(Number{0}, Number{kMaxMpTokenAmount / 1'000'000}, false, tesSUCCESS);
        // Over the share ceiling: the share amount overflows the MPT domain. C++ returns
        // tecPATH_DRY; the model's computeDeposit catches the overflow and returns the same.
        testVaultDepositIOU(
            Number{0}, Number{(kMaxMpTokenAmount / 1'000'000) + 1}, false, tecPATH_DRY);

        testVaultDepositIOU(Number{0}, Number{1}, true, tesSUCCESS);
        testVaultDepositIOU(Number{0}, Number{kMaxMpTokenAmount / 1'000'000}, true, tesSUCCESS);
        testVaultDepositIOU(
            Number{0}, Number{(kMaxMpTokenAmount / 1'000'000) + 1}, true, tecPATH_DRY);

        // IOU STAmount magnitude extremes (offset range is [kMinOffset, kMaxOffset] = [-96, 80]).
        testVaultDepositIOU(Number{0}, Number{9'999'999'999'999'999LL, 80}, true, tecPATH_DRY);
        testVaultDepositIOU(Number{0}, Number{1, -80}, true, tecPRECISION_LOSS);

        // roundedDepositAmount
        testRoundedDepositSuccess();
        testRoundedDepositBelowVaultScale(false);
        testRoundedDepositBelowVaultScale(true);
        // sanity: a normal deposit into the same non-empty vault still succeeds
        testVaultDepositIOU(Number{1, 12}, Number{1'000}, false, tesSUCCESS);

        // MPT: scale 0, sfMPTAmount and shares are int64, with kMaxMpTokenAmount == INT64_MAX.
        testVaultDepositMPT(0, 1, tesSUCCESS);
        testVaultDepositMPT(0, 1'000, tesSUCCESS);
        testVaultDepositMPT(0, kMaxMpTokenAmount, tesSUCCESS);  // deposit the type maximum
        testVaultDepositMPT(1'000, 1'000, tesSUCCESS);          // non-empty vault
        // Integer extremes: a big multiply (sharesTotal * amount) that lands outstanding shares
        // exactly on INT64_MAX
        testVaultDepositMPT(1, kMaxMpTokenAmount - 1, tesSUCCESS);
        testVaultDepositMPT(kMaxMpTokenAmount - 1, 1, tesSUCCESS);
        // (kMax/2)^2 / (kMax/2) rounds up a ULP in Number (~16 sig digits), so amountDeposit'
        // exceeds the deposit and C++ rejects with tecINTERNAL
        testVaultDepositMPT(kMaxMpTokenAmount / 2, kMaxMpTokenAmount / 2, tecINTERNAL);

        // Rounding-mode regression traps, these values catch potential rounding mode changes
        testVaultDepositIOU(Number{1, 12}, Number{100006, -4}, false, tesSUCCESS);
        testVaultDepositIOU(Number{1, 12}, Number{100001, -4}, false, tesSUCCESS);

        // Empty-vault share truncation (C++ truncates toward zero, not to-nearest):
        // 1.5e-6 USD * 1e6 scale = 1.5 shares -> 1.
        testVaultDepositIOU(Number{0}, Number{15, -7}, true, tesSUCCESS);
        // Zero-share deposit is rejected: 0.6e-6 USD * 1e6 = 0.6 shares -> 0 -> tecPRECISION_LOSS.
        testVaultDepositIOU(Number{0}, Number{6, -7}, true, tecPRECISION_LOSS);

        testVaultDepositExchangeRate();

        // Extreme NAV ratio AssetsTotal >> SharesTotal: a unit deposit buys zero shares.
        testVaultDepositUpdatedStateMPT(Number{1, 18}, 1, 1, tecPRECISION_LOSS);
        // AssetsTotal near the STAmount exponent ceiling: a small IOU deposit rounds to zero.
        testRoundedDepositUpdatedStateIOU(
            Number{9'999'999'999'999'999LL, 80}, Number{1}, tecPRECISION_LOSS);
        // IOU AssetsTotal + amount overflows
        testRoundedDepositOverflow();

        // Known discrepancies: each fails until the Lean model or C++ code is fixed
        // testVaultDepositMptCeiling();  // model tesSUCCESS where C++ gives tecPATH_DRY
        // testRoundedDepositTrustLineScale();  // model tesSUCCESS, C++ tecPRECISION_LOSS
        // testVaultDepositOvervaluedShares();  // model rounds up, C++ undercharges
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test
