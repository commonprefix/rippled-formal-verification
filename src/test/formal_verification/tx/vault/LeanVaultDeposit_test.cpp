#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

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
        Vault const state = readVaultState(env, vaultKeylet, asset);
        LeanRoundingResult const rounded = leanRoundedDepositAmount(state, amount);
        expectLawful(rounded);

        env(jtx::Vault::deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));

        std::optional<TER> const leanError =
            rounded.leanError.has_value() ? std::optional<TER>{tefEXCEPTION} : rounded.error;
        std::optional<TER> const expectedError =
            expected == tesSUCCESS ? std::nullopt : std::optional<TER>{expected};
        // The model result carries no asset, so compare the rounded value (a Number), not the
        // STAmount (whose operator== also checks currency).
        std::optional<Number> const leanAmount = rounded.amount
            ? std::optional<Number>{static_cast<Number>(*rounded.amount)}
            : std::nullopt;
        std::optional<Number> const expectedAmount = expected == tesSUCCESS
            ? std::optional<Number>{static_cast<Number>(amount)}
            : std::nullopt;
        BEAST_EXPECTS(
            leanError == expectedError,
            std::string("error lean=") + (leanError ? transToken(*leanError) : "none") +
                " expected " + (expectedError ? transToken(*expectedError) : "none"));
        BEAST_EXPECTS(
            leanAmount == expectedAmount,
            std::string("amount lean=") + (leanAmount ? to_string(*leanAmount) : "none") +
                " expected " + (expectedAmount ? to_string(*expectedAmount) : "none"));
    }

    // Model of doApply: leanVaultDeposit computes shares and the new vault state.
    void
    compareVaultDeposit(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& depositor,
        Asset const& asset,
        STAmount const& amount,
        TER expected,
        bool isDonation = false)
    {
        using namespace jtx;
        Vault const state = readVaultState(env, vaultKeylet, asset);
        LeanDepositResult const deposit = leanVaultDeposit(state, amount, isDonation);
        expectLawful(deposit);

        jtx::Vault::DepositArgs depositArgs{
            .depositor = depositor, .id = vaultKeylet.key, .amount = amount};
        if (isDonation)
            depositArgs.flags = tfVaultDonate;
        env(jtx::Vault::deposit(depositArgs), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));

        // A model raise surfaces as tefEXCEPTION, matching the C++ transactor.
        std::optional<TER> const leanError =
            deposit.leanError.has_value() ? std::optional<TER>{tefEXCEPTION} : deposit.error;
        std::optional<TER> const expectedError =
            expected == tesSUCCESS ? std::nullopt : std::optional<TER>{expected};
        BEAST_EXPECTS(
            leanError == expectedError,
            std::string("error lean=") + (leanError ? transToken(*leanError) : "none") +
                " expected " + (expectedError ? transToken(*expectedError) : "none"));

        if (cppTer != tesSUCCESS)
            return;

        auto const newVaultSle = env.le(vaultKeylet);
        auto const issuanceKeylet = keylet::mptokenIssuance(newVaultSle->at(sfShareMPTID));
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
        Number const cppLossUnrealized = newVaultSle->at(sfLossUnrealized);
        BEAST_EXPECTS(
            deposit.vault.lossUnrealized == cppLossUnrealized,
            "lossUnrealized lean=" + to_string(deposit.vault.lossUnrealized) +
                " cpp=" + to_string(cppLossUnrealized));
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
            env(jtx::Vault::deposit(
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
            env(jtx::Vault::deposit(
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
        env(jtx::Vault::deposit(
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
        env(jtx::Vault::deposit(
                {.depositor = issuer, .id = vaultKeylet.key, .amount = asset(Number{1, 12})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareRoundedDepositAmount(
            env, vaultKeylet, depositor, asset.raw(), asset(Number{1, -4}), tecPRECISION_LOSS);
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
        // After the donation 1 share = 1.667 drops. bob's 4-drop deposit buys 2 shares:
        // C++ charges round(3.33) = 3, the model charges ceil = 4.
        env(jtx::Vault::deposit(
                {.depositor = vaultOwner, .id = vaultKeylet.key, .amount = drops(3)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        env(jtx::Vault::deposit(
                {.depositor = vaultOwner,
                 .id = vaultKeylet.key,
                 .amount = drops(2),
                 .flags = tfVaultDonate}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareVaultDeposit(env, vaultKeylet, bob, xrpIssue(), drops(4), tesSUCCESS);
    }

    // Donating to a vault with no outstanding shares is rejected
    void
    testVaultDonationEmptyVault()
    {
        using namespace jtx;
        testcase("donation to empty vault");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        env.fund(XRP(1'000'000), vaultOwner);
        env.close();

        auto const vaultKeylet = createVault(env, vaultOwner, xrpIssue());
        compareVaultDeposit(
            env, vaultKeylet, vaultOwner, xrpIssue(), XRP(100), tecNO_PERMISSION, true);
    }

    // A deposit that pushes AssetsTotal past a non-zero AssetsMaximum is rejected with
    // tecLIMIT_EXCEEDED (a zero maximum means unlimited).
    void
    testVaultDepositLimitExceeded()
    {
        using namespace jtx;
        testcase("deposit exceeds assetsMaximum");

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
        env(pay(issuer, holder, asset(10'000)));
        env.close();

        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        // Cap the vault at 1000 with 1000 already in; a further 1000 deposit reaches 2000 > 1000.
        BEAST_EXPECT(
            updateVaultState(env, vaultKeylet, Number{1'000}, Number{1'000}, 1'000, Number{1'000}));
        compareVaultDeposit(env, vaultKeylet, holder, asset.raw(), asset(1'000), tecLIMIT_EXCEEDED);
    }

    // A donation to an insolvent vault (assetsTotal=0, sharesTotal>0) is NOT blocked
    void
    testVaultDonationInsolvent()
    {
        using namespace jtx;
        testcase("donation to insolvent vault");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), vaultOwner, issuer);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = vaultOwner});
        env.close();
        env(pay(issuer, vaultOwner, asset(10'000)));
        env.close();

        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{0}, Number{0}, 1'000'000));
        compareVaultDeposit(
            env, vaultKeylet, vaultOwner, asset.raw(), asset(1'000), tesSUCCESS, true);
    }

    // FV_M2_8 (both sides): the sfAssetsTotal += update re-rounds, dropping the sum's low
    // digits and lowering the share price. Assert the price does not fall.
    void
    testDepositDilution()
    {
        using namespace jtx;
        testcase("deposit lowers the share price (dilution)");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        Number const depositN{15'870'335, -4};  // 1587.0335
        auto const vaultKeylet = createDilutionVault(env, owner, issuer, holder, asset, depositN);

        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        STAmount const amount = asset(depositN);
        LeanDepositResult const lean = leanVaultDeposit(before, amount, false);
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean deposit error");

        env(jtx::Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        BEAST_EXPECTS(
            priceNotBelow(
                after.assetsTotal, after.sharesTotal, before.assetsTotal, before.sharesTotal),
            "C++ deposit lowered the share price");
        BEAST_EXPECTS(
            priceNotBelow(
                lean.vault.assetsTotal,
                lean.vault.sharesTotal,
                before.assetsTotal,
                before.sharesTotal),
            "model deposit lowered the share price");
    }

    // FV_M2_14: a donation rounds assetsTotal and assetsAvailable independently, so their
    // difference can drop below lossUnrealized and trip the invariant (tecINVARIANT_FAILED).
    void
    testDonationLossInvariant()
    {
        using namespace jtx;
        testcase("donation shrinks the loss gap and trips the invariant");

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), vaultOwner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(trust(vaultOwner, asset(1'000'000)));
        env.close();
        env(pay(issuer, vaultOwner, asset(1'000)));
        env.close();

        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = issuer, .id = vaultKeylet.key, .amount = asset(Number{100})}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // Valid state: lossUnrealized == assetsTotal - assetsAvailable == 0.999999999999995.
        Number const total{2'000'000'000'000'001LL, -15};      // 2.000000000000001
        Number const available{1'000'000'000'000'006LL, -15};  // 1.000000000000006
        Number const loss{999'999'999'999'995LL, -15};         // 0.999999999999995
        BEAST_EXPECT(
            updateVaultState(env, vaultKeylet, total, available, 100'000'000, Number{0}, loss));

        // Donating 50 rounds the two totals in opposite directions, decreasing the gap below the
        // loss. The donation is valid and should succeed, but the invariant fires.
        env(jtx::Vault::deposit(
                {.depositor = vaultOwner,
                 .id = vaultKeylet.key,
                 .amount = asset(Number{50}),
                 .flags = tfVaultDonate}),
            jtx::Ter(tesSUCCESS));
    }

    // FV_M2_15: an IOU deposit whose exact new total needs 17 significant digits rounds up
    // when stored, so sfAssetsTotal is credited more than the depositor paid.
    void
    testDepositOvercredit(Number const& seed, Number const& deposit, int vaultScale)
    {
        using namespace jtx;
        testcase(
            "deposit overcredit " + to_string(deposit) + " into " + to_string(seed) + " at scale " +
            std::to_string(vaultScale));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        jtx::Vault vault{env};
        auto [tx, vaultKeylet] = vault.create({.owner = owner, .asset = asset.raw()});
        tx[sfScale] = vaultScale;
        env(tx);
        env.close();
        env(jtx::Vault::deposit(
                {.depositor = issuer, .id = vaultKeylet.key, .amount = asset(seed)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // The exact new total needs 17 digits, C++ rounds sfAssetsTotal up, the model keeps it.
        compareVaultDeposit(env, vaultKeylet, issuer, asset.raw(), asset(deposit), tesSUCCESS);
    }

    // The round-trip charge is never re-rounded to the vault scale, so the totals move by
    // slightly more than the depositor pays (both C++ and the model).
    void
    testDepositAppliedDelta()
    {
        using namespace jtx;
        testcase("deposit moves the vault totals by a different amount than paid");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createAppliedDeltaVault(env, owner, issuer, holder, asset);

        // Leave the holder exactly 0.001: the debit below then subtracts without rounding,
        // so the balance diff is the exact amount accountSend moves.
        env(pay(holder, issuer, asset(Number{992, -3})));
        env.close();

        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        BEAST_EXPECT(before.assetsTotal == Number{3});

        // Deposit 0.001, an amount already on the vault grid.
        STAmount const amount = asset(Number{1, -3});
        LeanDepositResult const lean = leanVaultDeposit(before, amount, false);
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value() && !lean.error, "lean deposit failed");

        Number const holderBefore = iouBalance(env, holder, asset);
        env(jtx::Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        // C++: the vault must gain exactly what the depositor paid.
        Number const cppDelta = after.assetsTotal - before.assetsTotal;
        Number const paid = holderBefore - iouBalance(env, holder, asset);
        BEAST_EXPECTS(
            cppDelta == paid,
            "C++ booked " + to_string(cppDelta) + " but the depositor paid " + to_string(paid));

        // Model: the vault must gain exactly the charge it reports.
        Number const leanDelta = lean.vault.assetsTotal - before.assetsTotal;
        BEAST_EXPECTS(
            leanDelta == Number{lean.amountDeposit},
            "model booked " + to_string(leanDelta) + " but charged " +
                to_string(Number{lean.amountDeposit}));

        // C++: the paid amount must be on the vault scale.
        STAmount const paidRounded = roundToVaultScale(asset, before.assetsTotal, paid);
        BEAST_EXPECTS(
            Number{paidRounded} == paid,
            "the paid " + to_string(paid) + " re-rounds to " + to_string(Number{paidRounded}));

        // Model: its charge must be on the vault scale as well.
        LeanRoundingResult const chargeRounded =
            leanRoundedDepositAmount(before, lean.amountDeposit);
        expectLawful(chargeRounded);
        BEAST_EXPECTS(
            !chargeRounded.leanError.has_value() && chargeRounded.amount,
            "rounding the charge failed");
        BEAST_EXPECTS(
            chargeRounded.amount && Number{*chargeRounded.amount} == Number{lean.amountDeposit},
            "the charge " + to_string(Number{lean.amountDeposit}) + " re-rounds to " +
                (chargeRounded.amount ? to_string(Number{*chargeRounded.amount}) : "none"));
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

        // Insolvent vault (assetsTotal=0, sharesTotal>0): deposits are blocked with tecLOCKED.
        testVaultDepositUpdatedStateMPT(Number{0}, 1'000'000, 1'000, tecLOCKED);
        // Donation to an empty vault is blocked with tecNO_PERMISSION
        testVaultDonationEmptyVault();
        // Deposit over a non-zero maximum is blocked with tecLIMIT_EXCEEDED
        testVaultDepositLimitExceeded();

        // Known discrepancies, each fails until the C++ code is fixed.
        // clang-format off
        // testVaultDepositOvervaluedShares();  // FV_M2_3: model rounds up, C++ undercharges
        // testVaultDonationInsolvent();        // FV_M2_7: model tesSUCCESS, C++ tecLOCKED
        // testDepositDilution();               // FV_M2_8: deposit lowers the share price (both)
        // testDonationLossInvariant();         // FV_M2_14: donation trips the loss invariant
        // testDepositAppliedDelta();           // totals move by more than paid (both)

        // FV_M2_15: a deposit needing 17 digits rounds sfAssetsTotal up (associateAsset):
        // testDepositOvercredit(Number{9'999'999'999'999'999LL, -15}, Number{5}, 15);
        // testDepositOvercredit(Number{9'999'999'999'999'999LL, -6}, Number{1, -5}, 6);
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
