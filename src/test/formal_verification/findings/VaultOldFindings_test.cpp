#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/protocol/NumberFFI.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/protocol/STAmountFFI.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultCreateFFI.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultSetFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/numbers/helpers/NumberGenerators.h>
#include <test/formal_verification/tx/vault/CreateSetSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/base_uint.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/beast/hash/uhash.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/ledger/ApplyView.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Feature.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Issue.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/Rules.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/tx/apply.h>

#include <lean/lean.h>

#include <chrono>
#include <cstdint>
#include <exception>
#include <limits>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>

extern "C" lean_object*
lean_stamount_add(lean_object*, lean_object*, uint8_t);

namespace xrpl::test::formal_verification {

// The FV_M2 bugs found before fixed precision vaults (FV_M2_1 to FV_M2_19), vault cases with no
// bug ID and two gaps in the model. Most cases compare the Lean model with C++ on a staged vault.
// Calls that fail are commented out in runTests(), the rest run as regression tests.
class VaultOldFindings_test : public LeanSuite
{
    // The accounts of the two ledgers built in runTests. issuer_ is the depositor of the IOU
    // vaults, which skips the trust line checks. holder_ is the holder in the clawback tests.
    jtx::Account const owner_{"owner"};
    jtx::Account const issuer_{"issuer"};
    jtx::Account const depositor_{"depositor"};
    jtx::Account const holder_{"holder"};

    // Funds the accounts of the staged deposit and withdraw tests. Returns an MPT that owner_ and
    // depositor_ hold.
    Asset
    setupStagingAssets(jtx::Env& env)
    {
        using namespace jtx;
        env.fund(XRP(1'000'000), owner_, issuer_);
        env.fund(XRP(9'500'000'000), depositor_);
        env.close();

        MPTTester mptt{env, issuer_, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor_});
        mptt.authorize({.account = owner_});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer_, depositor_, mpt(9'200'000'000'000'000)));
        env(pay(issuer_, owner_, mpt(10'000)));
        env.close();
        return mpt.raw();
    }

    // Funds the accounts of the staged clawback tests. issuer_ can claw back its USD and the
    // returned MPT from holder_.
    Asset
    setupClawbackAssets(jtx::Env& env)
    {
        using namespace jtx;
        env.fund(XRP(1'000'000), owner_, issuer_, holder_);
        env.close();
        env(fset(issuer_, asfAllowTrustLineClawback));
        env.close();
        PrettyAsset const iou = issuer_["USD"];
        env(trust(holder_, iou(1'000'000)));
        env(pay(issuer_, holder_, iou(1'000)));

        MPTTester mptt{env, issuer_, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        mptt.authorize({.account = holder_});
        PrettyAsset const mpt = mptt.issuanceID();
        // The holder owns the largest MPT amount, which covers every staged clawback.
        env(pay(issuer_, holder_, mpt(static_cast<std::int64_t>(kMaxMpTokenAmount))));
        env.close();
        return mpt.raw();
    }

    // A vault of owner_ with a deposit of one base unit. The deposit creates the share MPToken
    // and the trust line that a staged state needs.
    Keylet
    createVaultWithDeposit(
        jtx::Env& env,
        Asset const& asset,
        jtx::Account const& depositor,
        std::optional<std::uint8_t> scale = std::nullopt)
    {
        Keylet const vault = createVault(env, owner_, asset, scale);
        env(jtx::Vault::deposit(
            {.depositor = depositor, .id = vault.key, .amount = vaultUnits(env, vault, 1)}));
        env.close();
        return vault;
    }

    // A USD vault where holder_ deposited 1e6 and owns every share, staged to the given totals
    // on the open ledger. issuer_ can claw back.
    Keylet
    createSoleHolderVault(
        jtx::Env& env,
        Number const& assetsTotal,
        Number const& lossUnrealized,
        std::uint64_t sharesTotal)
    {
        using namespace jtx;
        env.fund(XRP(1'000'000), owner_, issuer_, holder_);
        env.close();
        env(fset(issuer_, asfAllowTrustLineClawback));
        env.close();

        PrettyAsset const asset = issuer_["USD"];
        env(trust(holder_, asset(Number{2, 6})));
        env.close();
        env(pay(issuer_, holder_, asset(Number{1, 6})));
        env.close();

        Keylet const vaultKeylet = createVault(env, owner_, asset.raw());
        env(jtx::Vault::deposit(
            {.depositor = holder_, .id = vaultKeylet.key, .amount = asset(Number{1, 6})}));
        env.close();
        BEAST_EXPECT(stageSoleHolderVault(
            env, vaultKeylet, holder_, assetsTotal, lossUnrealized, sharesTotal));
        return vaultKeylet;
    }

    // A withdrawal in the model and on the open ledger, from the same state. Both must return
    // `expected` and, on success, leave the same vault.
    void
    compareWithdraw(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& holder,
        STAmount const& amount,
        TER expected)
    {
        Asset const asset = env.le(vaultKeylet)->at(sfAsset);
        LeanVaultResult const lean = leanVaultWithdraw(
            readVaultState(env, vaultKeylet, asset),
            amount,
            amount.asset() != asset,
            parentCloseTime(env),
            holderOwnsAllShares(env, vaultKeylet, holder),
            Number{fetchHolderShares(env, vaultKeylet, holder)});
        expectLawful(lean);

        env(jtx::Vault::withdraw({.depositor = holder, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(expected));
        TER const leanTer = lean.leanError ? TER{tefEXCEPTION} : lean.error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            leanTer == expected,
            "lean=" + transToken(leanTer) + " expected " + transToken(expected));
        // The vault is read before the close, which discards a staged state.
        if (env.ter() == tesSUCCESS && leanTer == tesSUCCESS)
            expectSameVault(*this, "", lean.vault, readVaultState(env, vaultKeylet, asset));
        env.close();
    }

    // A clawback by issuer_ from holder_ on a throwaway view of `staged`, and in the model. Both
    // must agree on the result and, on success, on the vault and on the amount recovered.
    std::pair<AppliedVaultTx, LeanVaultResult>
    checkClawback(jtx::Env& env, Keylet const& vault, StagedAmounts staged, STAmount const& amount)
    {
        // holder_ owns every share unless `staged` says otherwise.
        std::uint64_t const held = staged.holderShares.value_or(staged.sharesTotal);
        staged.holderShares = held;
        auto const tx = jtx::Vault::clawback(
            {.issuer = issuer_, .id = vault.key, .holder = holder_, .amount = amount});
        AppliedVaultTx const cpp = applyStaged(env, vault, holder_, staged, tx);
        STAmount const heldShares{shareIssue(env, vault), held};
        bool const ownsAll = staged.sharesTotal != 0 && held == staged.sharesTotal;
        LeanVaultResult const lean = leanVaultClawback(cpp.pre, amount, heldShares, ownsAll);
        std::string const at = sampleText(staged, amount);
        if (expectAgree(*this, at, cpp, lean) == tesSUCCESS && !lean.leanError && !lean.error)
        {
            Number const recovered = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;
            BEAST_EXPECTS(
                Number{lean.assets} == recovered,
                at + "recovered lean=" + to_string(Number{lean.assets}) +
                    " cpp=" + to_string(recovered));
        }
        return {cpp, lean};
    }

    // The result of a VaultCreate with the fields of `args`, on a throwaway view of the open
    // ledger.
    static TER
    applyCreate(
        jtx::Env& env,
        jtx::Account const& owner,
        Asset const& asset,
        VaultCreateArgs const& args)
    {
        jtx::Vault const vault{env};
        auto tx = std::get<0>(vault.create(
            {.owner = owner, .asset = asset, .earlyExitFeeRate = args.earlyExitFeeRate}));
        if (args.assetsMaximum)
            tx[sfAssetsMaximum] = *args.assetsMaximum;
        OpenView view{*env.current()};
        return xrpl::apply(env.app(), view, *env.jt(tx).stx, TapUnlimited, env.journal).ter;
    }

    // FV_M2_1: STAmount operator+ wraps to a negative amount when 1 drop is added to INT64_MAX
    // drops.
    void
    testXrpAddOverflow()
    {
        testcase("FV_M2_1 XRP add overflow");
        // The Lean model assumes all amendments.
        std::unordered_set<uint256, beast::Uhash<>> const amendments{
            featureMPTokensV2, featureSingleAssetVault, featureLendingProtocol};
        CurrentTransactionRulesGuard const rules{Rules{amendments}};
        NumberMantissaScaleGuard const scaleGuard(MantissaRange::MantissaScale::Large330);
        Number::RoundingMode const mode = Number::RoundingMode::ToNearest;

        // 1. INT64_MAX drops and 1 drop.
        constexpr auto kIntMax =
            static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max());
        STAmountPair const maxDrops = makeSTAmountPair(kNative, kIntMax, 0, 0);
        STAmountPair const oneDrop = makeSTAmountPair(kNative, 1, 0, 0);

        // 2. Add them in C++.
        bool cppThrew = false;
        STAmount cppSum;
        try
        {
            cppSum = maxDrops.cppSt + oneDrop.cppSt;
        }
        catch (std::exception const&)
        {
            cppThrew = true;
        }

        // 3. Add them in the model.
        NumberRoundModeGuard const modeGuard(mode);
        auto const lean = STAmountFFI::fromExcept(leanCall(
            lean_stamount_add,
            STAmountFFI::build(
                maxDrops.leanSt.numericType,
                maxDrops.leanSt.mValue,
                maxDrops.leanSt.mOffset,
                maxDrops.leanSt.isNegative),
            STAmountFFI::build(
                oneDrop.leanSt.numericType,
                oneDrop.leanSt.mValue,
                oneDrop.leanSt.mOffset,
                oneDrop.leanSt.isNegative),
            toLeanMode(mode)));

        // BUG: C++ returns INT64_MIN drops.
        BEAST_EXPECTS(
            cppThrew || cppSum.signum() > 0,
            "C++ XRP add at INT64_MAX wrapped to a negative value");
        BEAST_EXPECTS(
            !lean.ok || lean.isNegative == 0,
            "Lean XRP add at INT64_MAX wrapped to a negative value");
    }

    // FV_M2_3: a deposit is charged less than its new shares are worth, so the share price falls.
    void
    testDepositDilution()
    {
        using namespace jtx;
        testcase("FV_M2_3 deposit lowers the share price");

        // 1. A vault with AssetsTotal 900000123.333332 and 899999999876543 shares.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        Number const depositAmount{15'870'335, -4};
        auto const vaultKeylet =
            createDilutionVault(env, owner, issuer, holder, asset, depositAmount);

        // 2. The holder deposits 1587.0335 in the model and in C++.
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        STAmount const amount = asset(depositAmount);
        LeanVaultResult const lean = leanVaultDeposit(before, amount, false, parentCloseTime(env));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean deposit error");

        env(jtx::Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        // BUG: C++ charges 1587.033499 for shares worth 1587.0334997, so the share price falls.
        BEAST_EXPECTS(
            priceNotBelow(
                after.assetsTotal, after.sharesTotal, before.assetsTotal, before.sharesTotal),
            "C++ deposit lowered the share price");
        // BUG: the model charges the same amount.
        BEAST_EXPECTS(
            priceNotBelow(
                lean.vault.assetsTotal,
                lean.vault.sharesTotal,
                before.assetsTotal,
                before.sharesTotal),
            "model deposit lowered the share price");
    }

    // FV_M2_3: VaultDeposit variant. A 4 drop deposit at 5 drops per 3 shares is charged the same
    // amount by the model and C++.
    void
    testDepositOvervaluedShares(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        testcase("FV_M2_3 deposit overvalued shares");
        // 1. Stage a 3 drop seed and a 2 drop donation.
        StagedAmounts const staged{.available = vaultUnits(env, vault, 5), .sharesTotal = 3};
        // 2. Deposit 4 drops.
        TER const ter =
            checkDeposit(*this, env, vault, depositor, staged, vaultUnits(env, vault, 4));
        BEAST_EXPECTS(ter == tesSUCCESS, "cpp=" + transToken(ter));
    }

    // FV_M2_3: VaultWithdraw variant. One share at 5 drops per 3 shares pays the same amount in
    // the model and C++.
    void
    testWithdrawOvervaluedShares(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("FV_M2_3 withdraw overvalued shares");
        // 1. Stage a 3 drop seed by the holder and a 2 drop donation.
        StagedAmounts const staged{.available = vaultUnits(env, vault, 5), .sharesTotal = 3};
        // 2. Withdraw 1 share.
        STAmount const oneShare{shareIssue(env, vault), 1};
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, oneShare).ter;
        BEAST_EXPECTS(ter == tesSUCCESS, "cpp=" + transToken(ter));
    }

    // FV_M2_3: VaultClawback variant. Clawing back 2 units at 5 units per 3 shares recovers the
    // same amount in the model and C++.
    void
    testClawbackOvervaluedShares(jtx::Env& env, Keylet const& vault)
    {
        testcase("FV_M2_3 clawback overvalued shares");
        // 1. Stage a 3 unit deposit and a 2 unit donation.
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 5),
            .sharesTotal = 3,
            .pseudoHolding = true,
        };
        // 2. Claw back 2 units.
        auto const [cpp, lean] = checkClawback(env, vault, staged, vaultUnits(env, vault, 2));
        BEAST_EXPECTS(cpp.ter == tesSUCCESS, "cpp=" + transToken(cpp.ter));
    }

    // FV_M2_4: a 1e-6 withdrawal below the 1e-5 ULP of a staged AssetsTotal near 1e10 is rejected
    // with tecPRECISION_LOSS.
    void
    testWithdrawPrecisionLossStaged(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal)
    {
        testcase("FV_M2_4 STAGED withdraw 1e-6 from total " + to_string(assetsTotal));
        // 1. Stage the total. The holder owns the 1e9 shares of a deposit of 1'000.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = 10'000'000'000'000'009ULL,
            .holderShares = 1'000'000'000,
        };
        // 2. Withdraw 1e-6.
        STAmount const amount{asset, Number{1, -6}};
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, amount).ter;
        BEAST_EXPECTS(ter == tecPRECISION_LOSS, "cpp=" + transToken(ter));
    }

    // FV_M2_6: a sole shareholder's withdrawal waives LossUnrealized in doApply as in preclaim.
    void
    testWithdrawWaiveLoss()
    {
        using namespace jtx;
        testcase("FV_M2_6 withdraw sole shareholder waives unrealized loss");

        Env env(*this);
        Account const issuer{"issuer"};
        Account const lender{"lender"};
        Account const borrower{"borrower"};
        env.fund(XRP(1'000'000), issuer, lender, borrower);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        env(fset(issuer, asfDefaultRipple));
        env.close();
        env(trust(lender, asset(10'000'000)));
        env(trust(borrower, asset(10'000'000)));
        env.close();
        env(pay(issuer, lender, asset(1'000'000)));
        env(pay(issuer, borrower, asset(100'000)));
        env.close();

        // 1. A closed-ended vault where the lender is the sole shareholder.
        jtx::Vault const vault{env};
        auto const investmentWindow = std::chrono::seconds{1'000'000};
        auto const [createTx, vaultKeylet, subscriptionDate] = vault.createClosedEnded(
            {.owner = lender,
             .asset = asset.raw(),
             .subscriptionOffset = std::chrono::seconds{60},
             .investmentWindow = investmentWindow});
        env(createTx);
        env.close();
        env(jtx::Vault::deposit(
                {.depositor = lender, .id = vaultKeylet.key, .amount = asset(5'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        vault.closePastSubscription(subscriptionDate);

        // 2. Loan A of 3'333, impaired once its first payment is late.
        auto const brokerID =
            keylet::loanBroker(lender.id(), SeqProxy::rawSequence(env.seq(lender))).key;
        {
            using namespace loan_broker;
            env(set(lender, vaultKeylet.key), kDebtMaximum(asset(33'330).value()));
            env.close();
        }
        auto const sleBroker = env.le(keylet::loanBroker(brokerID));
        BEAST_EXPECT(sleBroker);
        auto const loanKeylet =
            keylet::loan(brokerID, SeqProxy::rawSequence(sleBroker->at(sfLoanSequence)));
        {
            using namespace loan;
            env(set(borrower, brokerID, 3'333),
                Sig(sfCounterpartySignature, lender),
                kPaymentTotal(2),
                kPaymentInterval(600),
                Fee(env.current()->fees().base * 2),
                jtx::Ter(tesSUCCESS));
            env.close();
            std::uint32_t const dueDate = env.le(loanKeylet)->at(sfNextPaymentDueDate);
            env.close(NetClock::time_point{NetClock::duration{dueDate + 1}});
            env(manage(lender, loanKeylet.key, tfLoanImpair), jtx::Ter(tesSUCCESS));
            env.close();
        }
        BEAST_EXPECT(env.le(vaultKeylet)->at(sfLossUnrealized) != Number{0});
        env.close(subscriptionDate + investmentWindow + std::chrono::seconds{1});

        // 3. The lender withdraws 100'000'000 shares after the redemption date.
        STAmount const shares{shareIssue(env, vaultKeylet), 100'000'000};
        compareWithdraw(env, vaultKeylet, lender, shares, tesSUCCESS);
    }

    // FV_M2_7: a donation to an insolvent vault (AssetsTotal 0, shares outstanding) succeeds.
    void
    testDonationInsolvent(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        testcase("FV_M2_7 donation to insolvent vault");
        StagedAmounts const insolvent{
            .available = vaultUnits(env, vault, 0),
            .sharesTotal = 1'000'000,
        };
        TER const ter =
            checkDeposit(*this, env, vault, owner, insolvent, vaultUnits(env, vault, 1'000), true);
        BEAST_EXPECTS(ter == tesSUCCESS, "cpp=" + transToken(ter));
    }

    // FV_M2_8: VaultWithdraw variant. A withdrawal does not lower the share price.
    void
    testWithdrawDilution()
    {
        using namespace jtx;
        testcase("FV_M2_8 withdraw lowers the share price");

        // 1. A vault with AssetsTotal 900000123.333332 and 899999999876543 shares.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createDilutionVault(env, owner, issuer, holder, asset);

        // 2. The holder withdraws 1'003'103'695 shares in the model and in C++.
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        STAmount const shares{shareIssue(env, vaultKeylet), 1'003'103'695};
        LeanVaultResult const lean = leanVaultWithdraw(
            before,
            shares,
            true,
            parentCloseTime(env),
            holderOwnsAllShares(env, vaultKeylet, holder),
            Number{fetchHolderShares(env, vaultKeylet, holder)});
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean withdraw error");

        env(jtx::Vault::withdraw({.depositor = holder, .id = vaultKeylet.key, .amount = shares}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        BEAST_EXPECTS(
            priceNotBelow(
                after.assetsTotal, after.sharesTotal, before.assetsTotal, before.sharesTotal),
            "C++ withdraw lowered the share price");
        BEAST_EXPECTS(
            priceNotBelow(
                lean.vault.assetsTotal,
                lean.vault.sharesTotal,
                before.assetsTotal,
                before.sharesTotal),
            "model withdraw lowered the share price");
    }

    // FV_M2_8: VaultClawback variant. A clawback does not lower the share price.
    void
    testClawbackDilution()
    {
        using namespace jtx;
        testcase("FV_M2_8 clawback lowers the share price");

        // 1. A vault with AssetsTotal 900000123.333332 and 899999999876543 shares.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createDilutionVault(env, owner, issuer, holder, asset);

        // 2. The issuer claws back 1000.917 in the model and in C++.
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        STAmount const amount = asset(Number{1'000'917, -3});
        STAmount const holderShares = fetchHolderShares(env, vaultKeylet, holder);
        LeanVaultResult const lean = leanVaultClawback(
            before, amount, holderShares, holderOwnsAllShares(env, vaultKeylet, holder));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean clawback error");

        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        BEAST_EXPECTS(
            priceNotBelow(
                after.assetsTotal, after.sharesTotal, before.assetsTotal, before.sharesTotal),
            "C++ clawback lowered the share price");
        BEAST_EXPECTS(
            priceNotBelow(
                lean.vault.assetsTotal,
                lean.vault.sharesTotal,
                before.assetsTotal,
                before.sharesTotal),
            "model clawback lowered the share price");
    }

    // FV_M2_9: a sole holder's withdrawal of all shares overshoots AssetsAvailable and fails with
    // tecINSUFFICIENT_FUNDS.
    void
    testWithdrawOvershoot()
    {
        using namespace jtx;
        testcase("FV_M2_9 withdraw all shares overshoots AssetsAvailable");

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
        env(pay(issuer, holder, asset(1'000)));
        env.close();

        // 1. An MPT vault where the holder deposited 1'000.
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // 2. Stage AssetsTotal = AssetsAvailable = INT64_MAX - 1 with 3 shares outstanding.
        std::int64_t const nearMax = 9'223'372'036'854'775'806LL;
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{nearMax}, Number{nearMax}, 3));

        // 3. The holder withdraws all 3 shares.
        STAmount const allShares{shareIssue(env, vaultKeylet), 3};
        // BUG: C++ and the model return tecINSUFFICIENT_FUNDS.
        compareWithdraw(env, vaultKeylet, holder, allShares, tesSUCCESS);
    }

    // FV_M2_10: an issuer VaultClawback with amount 0 claws back the holder's full balance.
    void
    testClawbackZeroAmountFullBalance(jtx::Env& env, Keylet const& vault)
    {
        testcase("FV_M2_10 issuer clawback with amount 0 claws the full balance");
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 1'000),
            .sharesTotal = 1'000,
            .pseudoHolding = true,
        };
        auto const [cpp, lean] = checkClawback(env, vault, staged, vaultUnits(env, vault, 0));
        BEAST_EXPECTS(cpp.ter == tesSUCCESS, "cpp=" + transToken(cpp.ter));
        BEAST_EXPECT(cpp.post.sharesTotal == Number{0});
    }

    // FV_M2_11: an issuer clawback of 4 units at 7 units per 5 shares recovers at most 4 units.
    void
    testClawbackOverRecover(jtx::Env& env, Keylet const& vault)
    {
        testcase("FV_M2_11 issuer clawback recovers more than requested");
        // 1. Stage a 5 unit deposit and a 2 unit donation at scale 0.
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 7),
            .sharesTotal = 5,
            .pseudoHolding = true,
        };
        // 2. Claw back 4 units.
        auto const [cpp, lean] = checkClawback(env, vault, staged, vaultUnits(env, vault, 4));
        BEAST_EXPECTS(cpp.ter == tesSUCCESS, "cpp=" + transToken(cpp.ter));
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean clawback error");
        BEAST_EXPECTS(
            cpp.pre.assetsTotal - cpp.post.assetsTotal <= Number{4},
            "C++ clawback recovered more than requested");
        BEAST_EXPECTS(
            static_cast<Number>(lean.assets) <= Number{4},
            "model clawback recovered more than requested");
    }

    // FV_M2_12: VaultWithdraw variant. Withdrawing one share worth less than the AssetsTotal ULP
    // is rejected with tecPRECISION_LOSS.
    void
    testWithdrawDustDebit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        std::uint64_t sharesTotal)
    {
        testcase("FV_M2_12 withdraw one dust share (total " + to_string(assetsTotal) + ")");
        // 1. Stage the totals. The holder owns the 1e12 shares of a deposit of 1e6.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = sharesTotal,
            .holderShares = 1'000'000'000'000,
        };
        // 2. Withdraw 1 share.
        STAmount const oneShare{shareIssue(env, vault), 1};
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, oneShare).ter;
        BEAST_EXPECTS(ter == tecPRECISION_LOSS, "cpp=" + transToken(ter));
    }

    // FV_M2_12: VaultClawback variant. A 2e-6 clawback below the ULP of the staged AssetsTotal is
    // rejected with tecPRECISION_LOSS.
    void
    testClawbackDustDebit(
        jtx::Env& env,
        Keylet const& vault,
        Number const& assetsTotal,
        std::uint64_t sharesTotal)
    {
        testcase("FV_M2_12 clawback one dust share (total " + to_string(assetsTotal) + ")");
        // 1. Stage the totals. The holder owns the 1e6 shares of a deposit of 1.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = sharesTotal,
            .holderShares = 1'000'000,
            .pseudoHolding = true,
        };
        // 2. Claw back 2e-6.
        auto const [cpp, lean] = checkClawback(env, vault, staged, STAmount{asset, Number{2, -6}});
        BEAST_EXPECTS(cpp.ter == tecPRECISION_LOSS, "cpp=" + transToken(cpp.ter));
    }

    // FV_M2_12: VaultClawback variant. A 1e-6 clawback below the 1e-5 ULP of a staged AssetsTotal
    // near 1e10 is rejected with tecPRECISION_LOSS.
    void
    testClawbackPrecisionLossStaged(jtx::Env& env, Keylet const& vault, Number const& assetsTotal)
    {
        testcase("FV_M2_12 STAGED clawback 1e-6 from total " + to_string(assetsTotal));
        // 1. Stage the total. The holder owns the 1e9 shares of a deposit of 1'000.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = 10'000'000'000'000'009ULL,
            .holderShares = 1'000'000'000,
            .pseudoHolding = true,
        };
        // 2. Claw back 1e-6.
        auto const [cpp, lean] = checkClawback(env, vault, staged, STAmount{asset, Number{1, -6}});
        BEAST_EXPECTS(cpp.ter == tecPRECISION_LOSS, "cpp=" + transToken(cpp.ter));
    }

    // FV_M2_13: a sole shareholder's withdrawal of all shares with LossUnrealized outstanding is
    // rejected with tecHAS_OBLIGATIONS.
    void
    testWithdrawFinalWithLoss(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        Number const& loss)
    {
        testcase(
            "FV_M2_13 full withdrawal of " + to_string(assetsTotal) + " with loss " +
            to_string(loss));
        // 1. Stage the loss, backed by the same amount of deployed assets. The holder owns the
        //    shares of a first deposit of the total, 1e6 for each unit.
        Asset const asset = env.le(vault)->at(sfAsset);
        STAmount const allShares{shareIssue(env, vault), assetsTotal * Number{1, 6}};
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal - loss},
            .deployed = STAmount{asset, loss},
            .loss = STAmount{asset, loss},
            .sharesTotal = allShares.mantissa(),
        };
        // 2. Withdraw all shares.
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, allShares).ter;
        BEAST_EXPECTS(ter == tecHAS_OBLIGATIONS, "cpp=" + transToken(ter));
    }

    // FV_M2_15: an IOU deposit whose new AssetsTotal is past the Open limit of 9e15 base units is
    // rejected with tecLIMIT_EXCEEDED.
    void
    testDepositPastOpenLimit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& issuer,
        Number const& seed,
        Number const& deposit)
    {
        int const vaultScale = env.le(vault)->at(sfScale);
        testcase(
            "FV_M2_15 deposit " + to_string(deposit) + " into " + to_string(seed) + " at scale " +
            std::to_string(vaultScale) + " passes the open limit");
        // 1. Stage the seed as a first deposit, which mints seed * 10^scale shares.
        Asset const asset = env.le(vault)->at(sfAsset);
        STAmount const shares{shareIssue(env, vault), seed * Number{1, vaultScale}};
        StagedAmounts const staged{
            .available = STAmount{asset, seed},
            .sharesTotal = shares.mantissa(),
        };
        // 2. Deposit past the limit.
        TER const ter = checkDeposit(*this, env, vault, issuer, staged, STAmount{asset, deposit});
        BEAST_EXPECTS(ter == tecLIMIT_EXCEEDED, "cpp=" + transToken(ter));
    }

    // FV_M2_15: VaultWithdraw variant. A 6e-6 withdrawal below the 1e-5 ULP of an AssetsTotal
    // staged at 1.2e10, past the Open limit, is rejected with tecPRECISION_LOSS.
    void
    testWithdrawAssetsStaged(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        Number const assetsTotal{1'234'567'890'123'456LL, -5};
        std::uint64_t const sharesTotal = 12'345'678'901'234'560ULL;
        Number const amount{6, -6};
        testcase(
            "FV_M2_15 STAGED withdraw IOU " + to_string(amount) + " from " +
            to_string(assetsTotal));
        // 1. Stage the total. The holder owns the 1e9 shares of a deposit of 1'000.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = sharesTotal,
            .holderShares = 1'000'000'000,
        };
        // 2. Withdraw 6e-6.
        TER const ter =
            checkWithdraw(*this, env, vault, holder, staged, STAmount{asset, amount}).ter;
        BEAST_EXPECTS(ter == tecPRECISION_LOSS, "cpp=" + transToken(ter));
    }

    // FV_M2_16: all shares but one are withdrawn from a scale 0 vault staged at 1e17, past the Open
    // limit. The model and C++ agree.
    void
    testWithdrawDrainsVault(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("FV_M2_16 partial withdrawal drains a scale-0 vault to zero");
        // 1. Stage AssetsTotal 1e17 with 1e17 shares, all owned by the holder.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, Number{1, 17}},
            .sharesTotal = 100'000'000'000'000'000ULL,
        };
        // 2. Withdraw all shares but one.
        STAmount const allButOne{shareIssue(env, vault), staged.sharesTotal - 1};
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, allButOne).ter;
        BEAST_EXPECTS(ter == tesSUCCESS, "cpp=" + transToken(ter));
    }

    // FV_M2_17: a full clawback from a sole holder with LossUnrealized 1'000 recovers
    // AssetsAvailable and keeps the lost part backed by shares.
    void
    testClawbackAllWithLoss()
    {
        testcase("FV_M2_17 clawback all with unrealized loss");

        // 1. A sole holder's vault staged to AssetsTotal 1e6, LossUnrealized 1'000 and 1e6 shares.
        jtx::Env env{*this};
        Number const loss{1'000};
        Keylet const vaultKeylet = createSoleHolderVault(env, Number{1'000'000}, loss, 1'000'000);

        // 2. The issuer claws back everything (amount 0).
        STAmount const zero = issuer_["USD"](0);
        env(jtx::Vault::clawback(
            {.issuer = issuer_, .id = vaultKeylet.key, .holder = holder_, .amount = zero}));

        // 3. Only the loss stays, backed by 1'000 shares. The ledger is not closed, which would
        //    discard the staged state.
        auto const sleVault = env.le(vaultKeylet);
        BEAST_EXPECT(sleVault->at(sfAssetsAvailable) == Number{0});
        BEAST_EXPECT(sleVault->at(sfAssetsTotal) == loss);
        BEAST_EXPECT(sleVault->at(sfLossUnrealized) == loss);
        auto const sleShares = env.le(keylet::mptokenIssuance(sleVault->at(sfShareMPTID)));
        BEAST_EXPECT(sleShares->at(sfOutstandingAmount) == 1'000);
    }

    // FV_M2_18: a full clawback of a 19 digit AssetsTotal burns every share, leaves a rounding
    // remainder and fails with tecINVARIANT_FAILED instead of tecPRECISION_LOSS.
    void
    testClawbackAllWithRemainder()
    {
        testcase("FV_M2_18 clawback all leaves a rounding remainder");

        // 1. A sole holder's vault staged to a 19 digit AssetsTotal and 7'000'025 shares.
        jtx::Env env{*this};
        Keylet const vaultKeylet = createSoleHolderVault(
            env, Number{3'141'592'653'589'793'238LL, -18}, Number{0}, 7'000'025);

        // 2. The issuer claws back everything (amount 0).
        STAmount const zero = issuer_["USD"](0);
        // BUG: C++ returns tecINVARIANT_FAILED.
        env(jtx::Vault::clawback(
                {.issuer = issuer_, .id = vaultKeylet.key, .holder = holder_, .amount = zero}),
            jtx::Ter(tecPRECISION_LOSS));
    }

    // FV_M2_19: VaultSet rejects an AssetsMaximum with more than 16 digits instead of rounding it.
    void
    testSetAssetsMaximumOver16Digits()
    {
        using namespace jtx;
        testcase("FV_M2_19 VaultSet AssetsMaximum over 16 digits");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        PrettyAsset const asset = issuer["USD"];
        env.trust(asset(1'000), owner);
        env(pay(issuer, owner, asset(200)));
        env.close();

        // 1. An IOU vault at the default scale.
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        Number const storedBefore = env.le(vaultKeylet)->at(sfAssetsMaximum);

        // 2. VaultSet with AssetsMaximum 1234567890123456.7 in the model and in C++.
        Number const submitted{12'345'678'901'234'567LL, -1};
        LawfulTerResult const lean = leanCanVaultUpdate(before, submitted);
        expectLawful(lean);
        BEAST_EXPECTS(
            !lean.leanError.has_value() && lean.ter == tecPRECISION_LOSS,
            "lean=" + transToken(lean.ter) + " expected " + transToken(tecPRECISION_LOSS));
        auto tx = jtx::Vault::set({.owner = owner, .id = vaultKeylet.key});
        tx[sfAssetsMaximum] = submitted;
        env(tx, jtx::Ter(tecPRECISION_LOSS));
        env.close();

        // 3. The stored AssetsMaximum is unchanged.
        Number const stored = env.le(vaultKeylet)->at(sfAssetsMaximum);
        BEAST_EXPECTS(
            stored == storedBefore,
            "AssetsMaximum changed: before=" + to_string(storedBefore) +
                " stored=" + to_string(stored));
    }

    // FV_M2_19: VaultCreate rejects an AssetsMaximum with more than 16 digits instead of rounding
    // it.
    void
    testCreateAssetsMaximumOver16Digits(jtx::Env& env, jtx::Account const& owner, Asset const& iou)
    {
        testcase("FV_M2_19 VaultCreate IOU maximum over 16 digits");

        // 1. VaultCreate with AssetsMaximum 1234567890123456.7 in the model.
        Number const submitted{12'345'678'901'234'567LL, -1};
        VaultCreateArgs const args{
            .assetsMaximum = submitted, .numericType = NumericTypeFFI::tagOf(iou)};
        LawfulTerResult const lean = leanCanVaultCreate(args, parentCloseTime(env));
        BEAST_EXPECTS(
            !lean.leanError.has_value() && lean.ter == tecPRECISION_LOSS,
            "lean=" + transToken(lean.ter) + " expected " + transToken(tecPRECISION_LOSS));

        // 2. The same VaultCreate in C++, on a throwaway view of the open ledger.
        TER const cppTer = applyCreate(env, owner, iou, args);
        BEAST_EXPECTS(
            cppTer == tecPRECISION_LOSS,
            "cpp=" + transToken(cppTer) + " expected " + transToken(tecPRECISION_LOSS));
    }

    // A deposit moves the vault totals by exactly the amount the depositor pays, in C++ and in the
    // model.
    void
    testDepositAppliedDelta()
    {
        using namespace jtx;
        testcase("deposit moves the vault totals by exactly the amount paid");

        // 1. A vault with AssetsTotal 3. The holder keeps exactly 0.001, so its balance moves by
        //    the exact amount the deposit takes.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createAppliedDeltaVault(env, owner, issuer, holder, asset);
        env(pay(holder, issuer, asset(Number{992, -3})));
        env.close();
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        BEAST_EXPECT(before.assetsTotal == Number{3});

        // 2. The holder deposits 0.001, an amount on the vault grid, in the model and in C++.
        STAmount const amount = asset(Number{1, -3});
        LeanVaultResult const lean = leanVaultDeposit(before, amount, false, parentCloseTime(env));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value() && !lean.error, "lean deposit failed");

        Number const holderBefore = iouBalance(env, holder, asset);
        env(jtx::Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        // 3. In C++ the vault gains exactly what the depositor paid.
        Number const cppDelta = after.assetsTotal - before.assetsTotal;
        Number const paid = holderBefore - iouBalance(env, holder, asset);
        BEAST_EXPECTS(
            cppDelta == paid,
            "C++ booked " + to_string(cppDelta) + " but the depositor paid " + to_string(paid));

        // 4. In the model the vault gains exactly the charge it reports.
        Number const leanDelta = lean.vault.assetsTotal - before.assetsTotal;
        BEAST_EXPECTS(
            leanDelta == Number{lean.assets},
            "model booked " + to_string(leanDelta) + " but charged " +
                to_string(Number{lean.assets}));

        // 5. The amount paid in C++ is on the vault scale.
        STAmount const paidRounded =
            roundToVaultGrid(asset, before.scale, before.assetsTotal, paid);
        BEAST_EXPECTS(
            Number{paidRounded} == paid,
            "the paid " + to_string(paid) + " re-rounds to " + to_string(Number{paidRounded}));

        // 6. The charge of the model is on the vault scale as well.
        LeanAmountResult const chargeRounded = leanRoundedDepositAmount(before, lean.assets);
        expectLawful(chargeRounded);
        BEAST_EXPECTS(
            !chargeRounded.leanError.has_value() && chargeRounded.amount,
            "rounding the charge failed");
        BEAST_EXPECTS(
            chargeRounded.amount && Number{*chargeRounded.amount} == Number{lean.assets},
            "the charge " + to_string(Number{lean.assets}) + " re-rounds to " +
                (chargeRounded.amount ? to_string(Number{*chargeRounded.amount}) : "none"));
    }

    // A withdrawal moves the vault totals by exactly the payout the holder receives, in C++ and in
    // the model.
    void
    testWithdrawAppliedDelta()
    {
        using namespace jtx;
        testcase("withdraw moves the vault totals by exactly the payout");

        // 1. A vault with AssetsTotal 3. The holder's balance is emptied, so it moves by the exact
        //    amount of the payout.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createAppliedDeltaVault(env, owner, issuer, holder, asset);
        env(pay(holder, issuer, asset(Number{993, -3})));
        env.close();
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        BEAST_EXPECT(before.assetsTotal == Number{3});

        // 2. The holder redeems a third of its 7e7 shares in the model and in C++.
        STAmount const shares{shareIssue(env, vaultKeylet), std::int64_t{23'333'333}};
        LeanVaultResult const lean = leanVaultWithdraw(
            before,
            shares,
            true,
            parentCloseTime(env),
            holderOwnsAllShares(env, vaultKeylet, holder),
            Number{fetchHolderShares(env, vaultKeylet, holder)});
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value() && !lean.error, "lean withdraw failed");

        Number const holderBefore = iouBalance(env, holder, asset);
        env(jtx::Vault::withdraw({.depositor = holder, .id = vaultKeylet.key, .amount = shares}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        // 3. In C++ the vault loses exactly what the holder received.
        Number const cppDelta = before.assetsTotal - after.assetsTotal;
        Number const received = iouBalance(env, holder, asset) - holderBefore;
        BEAST_EXPECTS(
            cppDelta == received,
            "C++ booked " + to_string(cppDelta) + " but the holder received " +
                to_string(received));

        // 4. In the model the vault loses exactly the payout it reports.
        Number const leanDelta = before.assetsTotal - lean.vault.assetsTotal;
        BEAST_EXPECTS(
            leanDelta == Number{lean.assets},
            "model booked " + to_string(leanDelta) + " but paid out " +
                to_string(Number{lean.assets}));

        // 5. The payout is on the vault scale. The model pays the same value here.
        STAmount const receivedRounded =
            roundToVaultGrid(asset, before.scale, before.assetsAvailable, -received);
        BEAST_EXPECTS(
            Number{receivedRounded} == received,
            "the paid out " + to_string(received) + " re-rounds to " +
                to_string(Number{receivedRounded}));
    }

    // A clawback moves the vault total by exactly the amount the issuer recovers, in C++ and in
    // the model.
    void
    testClawbackAppliedDelta()
    {
        using namespace jtx;
        testcase("clawback moves the vault total by exactly the recovery");

        // 1. A vault with AssetsTotal 3.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createAppliedDeltaVault(env, owner, issuer, holder, asset);
        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        BEAST_EXPECT(before.assetsTotal == Number{3});

        // 2. The issuer claws back 0.0001 from the holder in the model. The model and C++ agree
        //    on the recovery, so it stands in for the amount C++ moves.
        STAmount const amount = asset(Number{1, -4});
        LeanVaultResult const lean = leanVaultClawback(
            before,
            amount,
            fetchHolderShares(env, vaultKeylet, holder),
            holderOwnsAllShares(env, vaultKeylet, holder));
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value() && !lean.error, "lean clawback failed");
        Number const recovery{lean.assets};
        BEAST_EXPECTS((recovery == Number{999'857, -10}), to_string(recovery));

        // 3. The same clawback in C++.
        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = amount}),
            jtx::Ter(tesSUCCESS));
        env.close();
        Vault const after = readVaultState(env, vaultKeylet, asset.raw());

        // 4. In C++ the vault loses exactly the recovery.
        Number const cppDelta = before.assetsTotal - after.assetsTotal;
        BEAST_EXPECTS(
            cppDelta == recovery,
            "C++ booked " + to_string(cppDelta) + " but recovered " + to_string(recovery));

        // 5. In the model the vault loses the same amount.
        Number const leanDelta = before.assetsTotal - lean.vault.assetsTotal;
        BEAST_EXPECTS(
            leanDelta == recovery,
            "model booked " + to_string(leanDelta) + " but recovered " + to_string(recovery));

        // 6. The recovery is on the vault scale.
        STAmount const recoveryRounded =
            roundToVaultGrid(asset, before.scale, before.assetsAvailable, -recovery);
        BEAST_EXPECTS(
            Number{recoveryRounded} == recovery,
            "the recovery " + to_string(recovery) + " re-rounds to " +
                to_string(Number{recoveryRounded}));
    }

    // One share of an MPT vault worth 0.3 base units pays nothing, so the withdrawal is rejected
    // with tecPRECISION_LOSS.
    void
    testWithdrawZeroPayout(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        Number const assetsTotal{1'000};
        std::uint64_t const sharesTotal = 3'333;
        std::int64_t const shareAmount = 1;
        testcase(
            "withdraw updated-state MPT shares=" + std::to_string(shareAmount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", sharesTotal=" + std::to_string(sharesTotal) + ")");
        // 1. Stage the totals. The holder owns the 1'000 shares of a deposit of 1'000.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = sharesTotal,
            .holderShares = 1'000,
        };
        // 2. Withdraw 1 share.
        STAmount const shares{shareIssue(env, vault), shareAmount};
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, shares).ter;
        BEAST_EXPECTS(ter == tecPRECISION_LOSS, "cpp=" + transToken(ter));
    }

    // On a vault whose whole total is an unrealized loss, with two holders, a withdrawal by shares
    // burns the shares for nothing and a withdrawal by assets is rejected.
    void
    testWithdrawFromFullyImpairedVault(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder)
    {
        testcase("withdraw shares from a fully impaired vault with two holders");
        // 1. The holder deposited 1000 and another holder 10, then the whole total was lost.
        //    The deposits minted 1e6 shares for each unit.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, Number{0}},
            .deployed = STAmount{asset, Number{1'010}},
            .loss = STAmount{asset, Number{1'010}},
            .sharesTotal = 1'010'000'000,
            .holderShares = 1'000'000'000,
        };
        // 2. A withdrawal of 100'000'000 shares succeeds.
        STAmount const shares{shareIssue(env, vault), 100'000'000};
        TER const sharesTer = checkWithdraw(*this, env, vault, holder, staged, shares).ter;
        BEAST_EXPECTS(sharesTer == tesSUCCESS, "cpp=" + transToken(sharesTer));
        // 3. A withdrawal of 1 by assets converts to zero shares and is rejected.
        STAmount const one{asset, Number{1}};
        TER const assetsTer = checkWithdraw(*this, env, vault, holder, staged, one).ter;
        BEAST_EXPECTS(assetsTer == tecPRECISION_LOSS, "cpp=" + transToken(assetsTer));
    }

    // A holder that owns half the shares redeems one share more than it owns. The vault could pay
    // it, the holder's balance cannot.
    void
    testWithdrawMoreSharesThanHeld(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("withdraw more shares than the holder owns");
        // 1. Two holders deposited 1000 each, which minted 1e9 shares for each of them.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged{
            .available = STAmount{asset, Number{2'000}},
            .sharesTotal = 2'000'000'000,
            .holderShares = 1'000'000'000,
        };
        // 2. The holder withdraws its shares plus one.
        STAmount const tooMany{shareIssue(env, vault), 1'000'000'001};
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, tooMany).ter;
        BEAST_EXPECTS(ter == tecINSUFFICIENT_FUNDS, "cpp=" + transToken(ter));
    }

    // A withdrawal from a vault nobody deposited into. It has no shares, so nobody is the sole
    // holder.
    void
    testWithdrawFromEmptyVault(bool byShares, TER expected)
    {
        using namespace jtx;
        testcase(
            std::string("withdraw from an empty vault by ") + (byShares ? "shares" : "assets"));

        Env env(*this);
        Account const owner{"owner"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, holder);
        env.close();

        auto const vaultKeylet = createVault(env, owner, xrpIssue());
        STAmount const amount =
            byShares ? STAmount{shareIssue(env, vaultKeylet), 1} : STAmount{drops(100)};
        compareWithdraw(env, vaultKeylet, holder, amount, expected);
    }

    // Model gap: an EarlyExitFeeRate, even 0, on an open-ended vault. C++ preflight returns
    // temMALFORMED and the model creates the vault without the rate.
    void
    testCreateOpenEndedEarlyExitFee(jtx::Env& env, jtx::Account const& owner, Asset const& iou)
    {
        testcase("model gap: open-ended vault with an early-exit fee");
        for (std::uint32_t const rate : {5'000U, 0U})
        {
            // VaultCreate with the rate and no schedule, in C++ and in the model.
            VaultCreateArgs const args{
                .earlyExitFeeRate = rate, .numericType = NumericTypeFFI::tagOf(iou)};
            TER const cpp = applyCreate(env, owner, iou, args);
            LawfulTerResult const canCreate = leanCanVaultCreate(args, parentCloseTime(env));
            std::string const at = "fee " + std::to_string(rate) + " cpp=" + transToken(cpp) + ": ";
            BEAST_EXPECTS(cpp == temMALFORMED, at + "expected temMALFORMED");
            BEAST_EXPECTS(!canCreate.leanError.has_value(), at + "lean canCreate error");
            // GAP: the model creates the vault.
            BEAST_EXPECTS(
                leanVaultCreate(args).leanError == LeanError::notLawful,
                at + "preflight rejects the fields but the model creates the vault (canCreate " +
                    transToken(canCreate.ter) + ")");
        }
    }

    // Model gap: an AssetsMaximum past the largest amount of the asset. C++ preflight returns
    // temMALFORMED and the model creates the vault.
    void
    testCreateMaximumPastAssetRange(
        jtx::Env& env,
        jtx::Account const& owner,
        std::vector<Asset> const& assets)
    {
        for (Asset const& asset : assets)
        {
            std::string name = asset.holds<MPTIssue>() ? "MPT" : "IOU";
            if (asset.native())
                name = "XRP";
            testcase("model gap: create " + name + " maximum range-Sweep");
            // Each row has maximums around the largest amount of the asset: 1e17 drops of XRP,
            // 2^63 - 1 of an MPT, 9999999999999999e80 of an IOU.
            for (auto const& [cusp, cases] : maximumRangeCases(asset))
            {
                std::set<TER> seen;
                for (MaximumRangeCusp const& c : cases)
                {
                    Number const maximum{c.mantissa, static_cast<int>(c.exponent)};
                    VaultCreateArgs const args{
                        .assetsMaximum = maximum, .numericType = NumericTypeFFI::tagOf(asset)};
                    TER const cpp = applyCreate(env, owner, asset, args);
                    LawfulTerResult const canCreate =
                        leanCanVaultCreate(args, parentCloseTime(env));
                    LeanCreateResult const created = leanVaultCreate(args);
                    seen.insert(cpp);
                    std::string const at =
                        "maximum " + to_string(maximum) + " cpp=" + transToken(cpp) + ": ";
                    BEAST_EXPECTS(!canCreate.leanError.has_value(), at + "lean canCreate error");
                    if (isTemMalformed(cpp))
                    {
                        // GAP: the model creates the vault.
                        BEAST_EXPECTS(
                            created.leanError == LeanError::notLawful,
                            at + "preflight rejects the maximum but the model creates the vault " +
                                "(canCreate " + transToken(canCreate.ter) + ")");
                        continue;
                    }
                    BEAST_EXPECTS(canCreate.ter == cpp, at + "lean=" + transToken(canCreate.ter));
                    if (cpp == tesSUCCESS)
                        BEAST_EXPECTS(!created.leanError.has_value(), at + "lean create error");
                }
                expectCrossed(cusp, seen, {temMALFORMED});
            }
        }
    }

    void
    runTests() override
    {
        using namespace jtx;

        // Every staged test runs on a throwaway view of one of these two ledgers. The deposit and
        // withdraw tests use the first one.
        Env env{*this};
        PrettyAsset const iou = issuer_["USD"];
        Asset const mpt = setupStagingAssets(env);
        Keylet const xrpVault = createVaultWithDeposit(env, xrpIssue(), depositor_);
        Keylet const mptVault = createVaultWithDeposit(env, mpt, depositor_);
        Keylet const iouMinScaleVault =
            createVaultWithDeposit(env, iou, issuer_, kVaultMinimumIouScale);
        Keylet const iouDefaultScaleVault =
            createVaultWithDeposit(env, iou, issuer_, kVaultDefaultIouScale);
        Keylet const iouMaxScaleVault =
            createVaultWithDeposit(env, iou, issuer_, kFixedPrecisionVaultMaximumIouScale);

        // The clawback tests use the second one, where issuer_ can claw back from holder_.
        Env clawbackEnv{*this};
        Asset const clawbackMpt = setupClawbackAssets(clawbackEnv);
        Keylet const clawbackMptVault = createVaultWithDeposit(clawbackEnv, clawbackMpt, holder_);
        Keylet const clawbackIouMinScaleVault =
            createVaultWithDeposit(clawbackEnv, iou, holder_, kVaultMinimumIouScale);
        Keylet const clawbackIouDefaultScaleVault =
            createVaultWithDeposit(clawbackEnv, iou, holder_, kVaultDefaultIouScale);

        // Open bugs. Each call fails until the C++ code is fixed, so it is commented out.
        // clang-format off
        // testXrpAddOverflow();                // FV_M2_1
        // testDepositDilution();               // FV_M2_3
        // testWithdrawOvershoot();             // FV_M2_9
        // testClawbackAllWithRemainder();      // FV_M2_18

        // Cases that pass today, kept as regression tests.
        testDepositOvervaluedShares(env, xrpVault, depositor_);       // FV_M2_3
        testWithdrawOvervaluedShares(env, xrpVault, depositor_);      // FV_M2_3
        testClawbackOvervaluedShares(clawbackEnv, clawbackMptVault);  // FV_M2_3
        testWithdrawPrecisionLossStaged(env, iouDefaultScaleVault, issuer_, Number{1'000'000'000'000'001LL, -5});  // FV_M2_4
        testWithdrawPrecisionLossStaged(env, iouDefaultScaleVault, issuer_, Number{1'000'000'000'000'000LL, -5});  // FV_M2_4
        testWithdrawWaiveLoss();                // FV_M2_6
        testDonationInsolvent(env, mptVault, owner_);  // FV_M2_7
        testWithdrawDilution();                 // FV_M2_8
        testClawbackDilution();                 // FV_M2_8
        testClawbackZeroAmountFullBalance(clawbackEnv, clawbackMptVault);  // FV_M2_10
        testClawbackOverRecover(clawbackEnv, clawbackIouMinScaleVault);    // FV_M2_11
        testWithdrawDustDebit(env, iouDefaultScaleVault, issuer_, Number{2, 12}, 1'000'000'000'000'000'000ULL);   // FV_M2_12
        testWithdrawDustDebit(env, iouDefaultScaleVault, issuer_, Number{15, 12}, 9'200'000'000'000'000'000ULL);  // FV_M2_12
        testClawbackDustDebit(clawbackEnv, clawbackIouDefaultScaleVault, Number{2, 12}, 1'000'000'000'000'000'000ULL);   // FV_M2_12
        testClawbackDustDebit(clawbackEnv, clawbackIouDefaultScaleVault, Number{15, 12}, 9'200'000'000'000'000'000ULL);  // FV_M2_12
        testClawbackPrecisionLossStaged(clawbackEnv, clawbackIouDefaultScaleVault, Number{1'000'000'000'000'001LL, -5});  // FV_M2_12
        testClawbackPrecisionLossStaged(clawbackEnv, clawbackIouDefaultScaleVault, Number{1'000'000'000'000'000LL, -5});  // FV_M2_12
        testWithdrawFinalWithLoss(env, iouDefaultScaleVault, issuer_, Number{100}, Number{10});  // FV_M2_13
        testDepositPastOpenLimit(env, iouDefaultScaleVault, issuer_, Number{9'999'999'999'999'999LL, -6}, Number{1, -5});  // FV_M2_15
        testDepositPastOpenLimit(env, iouMaxScaleVault, issuer_, Number{8'999'999'999'999'999LL, -10}, Number{5});         // FV_M2_15
        testWithdrawAssetsStaged(env, iouDefaultScaleVault, issuer_);  // FV_M2_15
        testWithdrawDrainsVault(env, iouMinScaleVault, issuer_);  // FV_M2_16
        testClawbackAllWithLoss();              // FV_M2_17
        testSetAssetsMaximumOver16Digits();     // FV_M2_19
        testCreateAssetsMaximumOver16Digits(env, owner_, iou);  // FV_M2_19

        // Cases with no bug ID, kept as regression tests.
        testDepositAppliedDelta();
        testWithdrawAppliedDelta();
        testClawbackAppliedDelta();
        testWithdrawZeroPayout(env, mptVault, depositor_);
        testWithdrawFromFullyImpairedVault(env, iouDefaultScaleVault, issuer_);
        testWithdrawMoreSharesThanHeld(env, iouDefaultScaleVault, issuer_);
        testWithdrawFromEmptyVault(false, tecPRECISION_LOSS);
        testWithdrawFromEmptyVault(true, tecINSUFFICIENT_FUNDS);

        // Gaps in the model, not C++ bugs. Each call fails while the gap is open, so it is
        // commented out.
        // testCreateOpenEndedEarlyExitFee(env, owner_, iou);
        // testCreateMaximumPastAssetRange(env, owner_, {xrpIssue(), iou, mpt});
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(VaultOldFindings, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
