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
    void
    compareDeposit(
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
        LeanDepositResult const deposit = leanVaultDeposit(state, amount, false);

        env(Vault::deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!rounded.threw, "lean roundedDepositAmount raised");

        // The lean TER is the first error surfaced: roundedDepositAmount's rejection, else the
        // deposit's error.
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
            leanTer == expected,
            std::string("lean=") + transToken(leanTer) + " expected " + transToken(expected));

        if (cppTer != tesSUCCESS)
            return;

        // On success, the model's new vault state must equal the ledger's assetsTotal,
        // assetsAvailable and sharesTotal.
        BEAST_EXPECTS(!deposit.threw, "lean deposit raised on success");
        auto const newVaultSle = env.le(vaultKeylet);
        auto const issuanceKeylet = keylet::mptIssuance(newVaultSle->at(sfShareMPTID));
        Number const cppAssetsTotal = newVaultSle->at(sfAssetsTotal);
        Number const cppAssetsAvailable = newVaultSle->at(sfAssetsAvailable);
        Number const cppSharesTotal{
            static_cast<std::int64_t>(env.le(issuanceKeylet)->at(sfOutstandingAmount))};
        BEAST_EXPECTS(deposit.vault.assetsTotal == cppAssetsTotal, "assetsTotal mismatch");
        BEAST_EXPECTS(
            deposit.vault.assetsAvailable == cppAssetsAvailable, "assetsAvailable mismatch");
        BEAST_EXPECTS(deposit.vault.sharesTotal == cppSharesTotal, "sharesTotal mismatch");
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

        compareDeposit(env, vaultKeylet, depositor, asset, amount, expected);
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
    testDepositIOU(
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
    testUpdatedStateDepositMPT(
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
        compareDeposit(env, vaultKeylet, holder, asset.raw(), asset(amount), expected);
    }

    // Update an IOU vault to an extreme AssetsTotal so a small issuer deposit rounds to zero at
    // the vault scale.
    void
    testUpdatedStateDepositIOU(Number const& assetsTotal, Number const& amount, TER expected)
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
        compareDeposit(env, vaultKeylet, issuer, asset.raw(), asset(amount), expected);
    }

    // Discrepancy: a non-issuer deposit that rounds to zero at the depositor's trust-line scale is
    // rejected by C++ (tecPRECISION_LOSS) but succeeds in the model (out of scope).
    void
    testDepositTrustLineScale()
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
        // A large holder balance gives a coarse trust-line scale (ULP ~ 1e-3), so a 1e-6 deposit
        // vanishes at that scale.
        env(trust(holder, asset(1'000'000'000'000'000LL)));
        env.close();
        env(pay(issuer, holder, asset(Number{1, 12})));
        env.close();

        runVaultDeposit(
            env,
            vaultOwner,
            issuer,
            holder,
            asset.raw(),
            asset(Number{0}),
            asset(Number{1, -6}),
            tecPRECISION_LOSS);
    }

    // Discrepancy: the model does not model the MPT mint ceiling. A deposit that would push
    // outstanding shares past INT64_MAX succeeds where C++ returns tecPATH_DRY.
    void
    testDepositMptCeiling()
    {
        testUpdatedStateDepositMPT(
            Number{static_cast<std::int64_t>(kMaxMpTokenAmount)},
            kMaxMpTokenAmount,
            1'000,
            tecPATH_DRY);
    }

    // Discrepancy: the model does not guard a negative AssetsTotal; the deposit succeeds where C++
    // returns tecINTERNAL.
    void
    testDepositNegativeAssetsTotal()
    {
        testUpdatedStateDepositMPT(Number{-5}, 5, 1, tecINTERNAL);
    }

    // Discrepancy: AssetsTotal + amount near the IOU maximum overflows; the model raises where C++
    // catches it as tefEXCEPTION.
    void
    testDepositArithmeticOverflow()
    {
        testUpdatedStateDepositIOU(
            Number{9'999'999'999'999'999LL, 80}, Number{9'999'999'999'999'999LL, 80}, tefEXCEPTION);
    }

    // Finding (C++ bug): a deposit charges round-to-nearest, so a deposit into a vault
    // can be undercharged, overvaluing the new shares and diluting existing holders.
    void
    testDepositOvervaluedShares()
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

        compareDeposit(env, vaultKeylet, bob, xrpIssue(), drops(4), tesSUCCESS);
    }

    void
    runTests() override
    {
        using namespace jtx;

        // XRP: scale 0, no share overflow within the XRP domain.
        testDepositXRP(XRP(0), drops(1), tesSUCCESS);  // minimum deposit
        testDepositXRP(XRP(0), XRP(1'000), tesSUCCESS);
        testDepositXRP(XRP(0), XRP(80'000'000'000), tesSUCCESS);
        testDepositXRP(XRP(1'000), XRP(1'000), tesSUCCESS);  // non-empty vault
        testDepositXRP(XRP(1'000), drops(1), tesSUCCESS);    // minimum deposit, non-empty

        // IOU: default vault scale 6, so shares ~ amount * 1e6; over kMaxMpTokenAmount / 1e6 the
        // share amount overflows.
        testDepositIOU(Number{0}, Number{1}, false, tesSUCCESS);
        testDepositIOU(Number{0}, Number{1'000}, false, tesSUCCESS);
        testDepositIOU(Number{0}, Number{kMaxMpTokenAmount / 1'000'000}, false, tesSUCCESS);
        // Over the share ceiling: the share amount overflows the MPT domain. C++ returns
        // tecPATH_DRY; the model's computeDeposit catches the overflow and returns the same.
        testDepositIOU(Number{0}, Number{(kMaxMpTokenAmount / 1'000'000) + 1}, false, tecPATH_DRY);

        testDepositIOU(Number{0}, Number{1}, true, tesSUCCESS);
        testDepositIOU(Number{0}, Number{kMaxMpTokenAmount / 1'000'000}, true, tesSUCCESS);
        testDepositIOU(Number{0}, Number{(kMaxMpTokenAmount / 1'000'000) + 1}, true, tecPATH_DRY);

        // IOU STAmount magnitude extremes (offset range is [kMinOffset, kMaxOffset] = [-96, 80]).
        testDepositIOU(Number{0}, Number{9'999'999'999'999'999LL, 80}, true, tecPATH_DRY);
        testDepositIOU(Number{0}, Number{1, -80}, true, tecPRECISION_LOSS);

        // Precision loss: a sub-ULP deposit into a large vault rounds to zero at the vault scale.
        // Vault holds 1e12 USD -> ULP 1e-3; depositing 1e-4 rounds to zero -> tecPRECISION_LOSS.
        testDepositIOU(Number{1, 12}, Number{1, -4}, false, tecPRECISION_LOSS);
        testDepositIOU(Number{1, 12}, Number{1, -4}, true, tecPRECISION_LOSS);
        // sanity: a normal deposit into the same non-empty vault still succeeds
        testDepositIOU(Number{1, 12}, Number{1'000}, false, tesSUCCESS);

        // MPT: scale 0, sfMPTAmount and shares are int64, with kMaxMpTokenAmount == INT64_MAX.
        testDepositMPT(0, 1, tesSUCCESS);
        testDepositMPT(0, 1'000, tesSUCCESS);
        testDepositMPT(0, kMaxMpTokenAmount, tesSUCCESS);  // deposit the type maximum
        testDepositMPT(1'000, 1'000, tesSUCCESS);          // non-empty vault
        // Integer extremes: a big multiply (sharesTotal * amount) that lands outstanding shares
        // exactly on INT64_MAX
        testDepositMPT(1, kMaxMpTokenAmount - 1, tesSUCCESS);
        testDepositMPT(kMaxMpTokenAmount - 1, 1, tesSUCCESS);
        // (kMax/2)^2 / (kMax/2) rounds up a ULP in Number (~16 sig digits), so amountDeposit'
        // exceeds the deposit and C++ rejects with tecINTERNAL
        testDepositMPT(kMaxMpTokenAmount / 2, kMaxMpTokenAmount / 2, tecINTERNAL);

        // Rounding-mode regression traps, these values catch potential rounding mode changes
        testDepositIOU(Number{1, 12}, Number{100006, -4}, false, tesSUCCESS);
        testDepositIOU(Number{1, 12}, Number{100001, -4}, false, tesSUCCESS);

        // Empty-vault share truncation (C++ truncates toward zero, not to-nearest):
        // 1.5e-6 USD * 1e6 scale = 1.5 shares -> 1.
        testDepositIOU(Number{0}, Number{15, -7}, true, tesSUCCESS);
        // Zero-share deposit is rejected: 0.6e-6 USD * 1e6 = 0.6 shares -> 0 -> tecPRECISION_LOSS.
        testDepositIOU(Number{0}, Number{6, -7}, true, tecPRECISION_LOSS);

        testDepositExchangeRate();

        // Extreme NAV ratio AssetsTotal >> SharesTotal: a unit deposit buys zero shares.
        testUpdatedStateDepositMPT(Number{1, 18}, 1, 1, tecPRECISION_LOSS);
        // AssetsTotal near the STAmount exponent ceiling: a small IOU deposit rounds to zero.
        testUpdatedStateDepositIOU(
            Number{9'999'999'999'999'999LL, 80}, Number{1}, tecPRECISION_LOSS);

        // Known discrepancies: each fails until the model is fixed; uncomment to verify.
        // testDepositMptCeiling();          // model tesSUCCESS where C++ gives tecPATH_DRY
        // testDepositNegativeAssetsTotal(); // model tesSUCCESS where C++ gives tecINTERNAL
        // testDepositArithmeticOverflow();  // model raises where C++ gives tefEXCEPTION
        // testDepositTrustLineScale();      // model tesSUCCESS where C++ gives tecPRECISION_LOSS
        // testDepositOvervaluedShares();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test
