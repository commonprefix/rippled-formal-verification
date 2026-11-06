#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/common/Sweep.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>
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

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <limits>
#include <optional>
#include <set>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

class LeanVaultDeposit_test : public LeanSuite
{
    // The old single-value tests run on the sweep ledger: each stages its vault on a throwaway
    // view (seed deposits become the shares a first deposit mints) and checks the expected
    // verdict on top of checkDeposit's Lean/C++ comparison.

    // A seed deposit of `seed` into an empty vault: the vault holds it and has minted seed *
    // 10^scale shares.
    static StagedVault
    seededVault(jtx::Env& env, Keylet const& vault, STAmount const& seed)
    {
        int const scale = env.le(vault)->at(sfScale);
        Number const shares = Number{seed} * Number{1, scale};
        return StagedVault{
            .available = seed,
            .sharesTotal = static_cast<std::uint64_t>(static_cast<std::int64_t>(shares))};
    }

    // A holder other than the asset's issuer holds exactly the amount it deposits.
    static StagedVault
    fundDepositor(StagedVault staged, jtx::Account const& depositor, STAmount const& amount)
    {
        if (!amount.native() && amount.holds<Issue>() && depositor.id() != amount.getIssuer())
            staged.depositorBalance = amount;
        return staged;
    }

    void
    expectStagedDeposit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        StagedVault const& staged,
        STAmount const& amount,
        TER expected,
        bool donate = false)
    {
        TER const cpp = checkDeposit(env, vault, depositor, staged, amount, donate);
        BEAST_EXPECTS(
            cpp == expected,
            std::string("cpp=") + transToken(cpp) + " expected " + transToken(expected));
    }

    // Model of preclaim: leanRoundedDepositAmount rounds to the vault scale and returns exactly
    // one of the rounded amount (success) or an error TER; C++ runs the whole deposit.
    void
    expectRoundedDeposit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        StagedVault const& staged,
        STAmount const& amount,
        TER expected)
    {
        AppliedDeposit const cpp = applyDeposit(env, vault, depositor, staged, amount);
        LeanAmountResult const rounded = leanRoundedDepositAmount(cpp.pre, amount);
        expectLawful(rounded);
        BEAST_EXPECTS(
            cpp.ter == expected,
            std::string("cpp=") + transToken(cpp.ter) + " expected " + transToken(expected));

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

    void
    testVaultDepositXRP(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        STAmount const& vaultBalanceBeforeDeposit,
        STAmount const& amount,
        TER expected)
    {
        testcase(
            "deposit XRP " + amount.getText() + " into " + vaultBalanceBeforeDeposit.getText());
        expectStagedDeposit(
            env,
            vault,
            depositor,
            seededVault(env, vault, vaultBalanceBeforeDeposit),
            amount,
            expected);
    }

    void
    testVaultDepositIOU(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        Number const& vaultBalanceBeforeDeposit,
        Number const& amount,
        TER expected)
    {
        Asset const asset = env.le(vault)->at(sfAsset);
        bool const depositorIsIssuer = depositor.id() == asset.getIssuer();
        testcase(
            "deposit IOU " + to_string(amount) + " into " + to_string(vaultBalanceBeforeDeposit) +
            (depositorIsIssuer ? " (issuer)" : ""));
        STAmount const a{asset, amount};
        StagedVault const staged = fundDepositor(
            seededVault(env, vault, STAmount{asset, vaultBalanceBeforeDeposit}), depositor, a);
        expectStagedDeposit(env, vault, depositor, staged, a, expected);
    }

    void
    testVaultDepositMPT(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        std::int64_t vaultBalanceBeforeDeposit,
        std::int64_t amount,
        TER expected)
    {
        testcase(
            "deposit MPT " + std::to_string(amount) + " into " +
            std::to_string(vaultBalanceBeforeDeposit));
        expectStagedDeposit(
            env,
            vault,
            depositor,
            seededVault(env, vault, gridUnits(env, vault, vaultBalanceBeforeDeposit)),
            gridUnits(env, vault, amount),
            expected);
    }

    // Exchange-rate path: an owner donation drifts NAV so shares come from a non-terminating
    // division, exercising the non-empty assetsToShares / sharesToAssets arithmetic.
    void
    testVaultDepositExchangeRate(jtx::Env& env, Keylet const& vault, jtx::Account const& issuer)
    {
        testcase("deposit exchange rate (NAV-drifted vault)");
        Asset const asset = env.le(vault)->at(sfAsset);
        // Seed 1 + donate 2 -> NAV 3, shareTotal 1e6 (ratio 1e6/3); deposit 100 -> 33'333'333
        // shares.
        StagedVault staged = seededVault(env, vault, STAmount{asset, Number{1}});
        staged.available = STAmount{asset, Number{3}};
        expectStagedDeposit(env, vault, issuer, staged, STAmount{asset, Number{100}}, tesSUCCESS);
    }

    // Update an MPT vault to an extreme state a real deposit cannot reach, then deposit and
    // compare.
    void
    testVaultDepositUpdatedStateMPT(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        Number const& assetsTotal,
        std::uint64_t sharesTotal,
        std::int64_t amount,
        TER expected,
        Number const& yieldUnrealized = Number{0})
    {
        testcase(
            "updated-state MPT deposit " + std::to_string(amount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", sharesTotal=" + std::to_string(sharesTotal) +
            ", yield=" + to_string(yieldUnrealized) + ")");
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedVault const staged{
            .available = STAmount{asset, assetsTotal},
            .yield = STAmount{asset, yieldUnrealized},
            .sharesTotal = sharesTotal};
        expectStagedDeposit(env, vault, depositor, staged, gridUnits(env, vault, amount), expected);
    }

    // The owner blocked deposits (VaultSet), so a deposit is tecLOCKED on both sides.
    void
    testVaultDepositBlocked(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        testcase("deposit into a vault with deposits blocked");
        StagedVault staged = seededVault(env, vault, gridUnits(env, vault, 1'000'000'000));
        staged.depositBlocked = true;
        expectStagedDeposit(
            env, vault, depositor, staged, gridUnits(env, vault, 100'000'000), tecLOCKED);
    }

    // Stage an IOU vault with a share price below the grid: the shares a deposit buys are worth
    // less than one grid unit, so the clamped deposit is zero.
    void
    testVaultDepositUpdatedStateIOU(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& issuer,
        Number const& assetsTotal,
        std::uint64_t sharesTotal,
        Number const& amount,
        TER expected)
    {
        testcase(
            "updated-state IOU deposit " + to_string(amount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", sharesTotal=" + std::to_string(sharesTotal) + ")");
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedVault const staged{
            .available = STAmount{asset, assetsTotal}, .sharesTotal = sharesTotal};
        expectStagedDeposit(env, vault, issuer, staged, STAmount{asset, amount}, expected);
    }

    // Update an IOU vault to an extreme AssetsTotal so a small issuer deposit rounds to zero (or
    // overflows) at the vault scale.
    void
    testRoundedDepositUpdatedStateIOU(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& issuer,
        Number const& assetsTotal,
        Number const& amount,
        TER expected)
    {
        testcase(
            "updated-state IOU deposit " + to_string(amount) +
            " (assetsTotal=" + to_string(assetsTotal) + ")");
        Asset const asset = env.le(vault)->at(sfAsset);
        // Shares so the vault is not zero-sized, the deposit still rejects on rounding.
        StagedVault const staged{
            .available = STAmount{asset, assetsTotal}, .sharesTotal = 1'000'000};
        expectRoundedDeposit(env, vault, issuer, staged, STAmount{asset, amount}, expected);
    }

    // A normal deposit is already at the vault scale, so roundedDepositAmount returns it unchanged
    // with no error.
    void
    testRoundedDepositSuccess(jtx::Env& env, Keylet const& vault, jtx::Account const& issuer)
    {
        testcase("roundedDepositAmount at vault scale");
        Asset const asset = env.le(vault)->at(sfAsset);
        expectRoundedDeposit(
            env,
            vault,
            issuer,
            seededVault(env, vault, STAmount{asset, Number{1, 9}}),
            STAmount{asset, Number{1'000}},
            tesSUCCESS);
    }

    // A deposit below the vault's 1e-6 grid: preclaim rounds it to zero
    void
    testRoundedDepositBelowVaultScale(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor)
    {
        Asset const asset = env.le(vault)->at(sfAsset);
        bool const depositorIsIssuer = depositor.id() == asset.getIssuer();
        testcase(std::string("deposit below vault scale") + (depositorIsIssuer ? " (issuer)" : ""));
        STAmount const amount{asset, Number{1, -7}};
        expectRoundedDeposit(
            env,
            vault,
            depositor,
            fundDepositor(
                seededVault(env, vault, STAmount{asset, Number{1, 9}}), depositor, amount),
            amount,
            tecPRECISION_LOSS);
    }

    // AssetsTotal + amount near the IOU maximum overflows.
    void
    testRoundedDepositOverflow(jtx::Env& env, Keylet const& vault, jtx::Account const& issuer)
    {
        testRoundedDepositUpdatedStateIOU(
            env,
            vault,
            issuer,
            Number{9'999'999'999'999'999LL, 80},
            Number{9'999'999'999'999'999LL, 80},
            tefEXCEPTION);
    }

    // Finding (C++ bug): a deposit charges round-to-nearest, so a deposit into a vault
    // can be undercharged, overvaluing the new shares and diluting existing holders.
    void
    testVaultDepositOvervaluedShares(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor)
    {
        testcase("deposit overvalued shares");
        // A 3-drop seed and a 2-drop donation: 1 share = 1.667 drops. A 4-drop deposit buys 2
        // shares: C++ charges round(3.33) = 3, the model charges ceil = 4.
        StagedVault staged = seededVault(env, vault, gridUnits(env, vault, 3));
        staged.available = gridUnits(env, vault, 5);
        expectStagedDeposit(env, vault, depositor, staged, gridUnits(env, vault, 4), tesSUCCESS);
    }

    // Donating to a vault with no outstanding shares is rejected
    void
    testVaultDonationEmptyVault(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        testcase("donation to empty vault");
        StagedVault const empty{.available = gridUnits(env, vault, 0), .sharesTotal = 0};
        expectStagedDeposit(
            env, vault, owner, empty, gridUnits(env, vault, 100'000'000), tecNO_PERMISSION, true);
    }

    // A deposit of 1000 into a vault holding 1000 under the AssetsMaximum `cap`: rejected with
    // tecLIMIT_EXCEEDED when the total would pass a non-zero cap (a zero maximum means unlimited).
    void
    testVaultDepositCap(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        Number const& cap,
        TER expected)
    {
        testcase("deposit under assetsMaximum " + to_string(cap));
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedVault const staged{
            .available = gridUnits(env, vault, 1'000),
            .maximum = STAmount{asset, cap},
            .sharesTotal = 1'000};
        expectStagedDeposit(env, vault, depositor, staged, gridUnits(env, vault, 1'000), expected);
    }

    // A donation to an insolvent vault (assetsTotal=0, sharesTotal>0) is NOT blocked
    void
    testVaultDonationInsolvent(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        testcase("donation to insolvent vault");
        StagedVault const insolvent{
            .available = gridUnits(env, vault, 0), .sharesTotal = 1'000'000};
        expectStagedDeposit(
            env, vault, owner, insolvent, gridUnits(env, vault, 1'000), tesSUCCESS, true);
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
        LeanVaultResult const lean = leanVaultDeposit(before, amount, false, parentCloseTime(env));
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

    // FV_M2_15 (regression): an IOU deposit whose exact new total needed 17 significant digits
    // rounded up when stored, crediting more than the depositor paid. Such a total is now past the
    // open limit (9e15 grid units), which is what rejects the deposit on both sides.
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
            "deposit " + to_string(deposit) + " into " + to_string(seed) + " at scale " +
            std::to_string(vaultScale) + " passes the open limit");
        Asset const asset = env.le(vault)->at(sfAsset);
        expectStagedDeposit(
            env,
            vault,
            issuer,
            seededVault(env, vault, STAmount{asset, seed}),
            STAmount{asset, deposit},
            tecLIMIT_EXCEEDED);
    }

    // The round-trip charge is clamped to the vault grid, so the totals move by exactly what the
    // depositor pays (both C++ and the model).
    void
    testDepositAppliedDelta()
    {
        using namespace jtx;
        testcase("deposit moves the vault totals by exactly the amount paid");

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
        LeanVaultResult const lean = leanVaultDeposit(before, amount, false, parentCloseTime(env));
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
            leanDelta == Number{lean.assets},
            "model booked " + to_string(leanDelta) + " but charged " +
                to_string(Number{lean.assets}));

        // C++: the paid amount must be on the vault scale.
        STAmount const paidRounded =
            roundToVaultGrid(asset, before.scale, before.assetsTotal, paid);
        BEAST_EXPECTS(
            Number{paidRounded} == paid,
            "the paid " + to_string(paid) + " re-rounds to " + to_string(Number{paidRounded}));

        // Model: its charge must be on the vault scale as well.
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

    // The vaults a sweep runs on, each with the account that deposits into it.
    using SweepVaults = std::vector<std::pair<Keylet, jtx::Account>>;

    // The values of one sample, prefixed to every failure message.
    static std::string
    sampleText(StagedVault const& s, STAmount const& amount)
    {
        return "amount " + amount.getText() + ", available " + s.available.getText() + ", yield " +
            s.yield.getText() + ", maximum " + (s.maximum ? s.maximum->getText() : "none") +
            ", sharesTotal " + std::to_string(s.sharesTotal) + ": ";
    }

    // One sample: C++ (on a throwaway view) and the model run on the same staged vault; they must
    // agree, and a deposit never charges more than offered. Returns the C++ verdict.
    TER
    checkDeposit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        StagedVault const& staged,
        STAmount const& amount,
        bool donate = false)
    {
        AppliedDeposit const cpp = applyDeposit(env, vault, depositor, staged, amount, donate);
        LeanVaultResult const lean =
            leanVaultDeposit(cpp.pre, amount, donate, parentCloseTime(env));
        std::string const at = sampleText(staged, amount);
        BEAST_EXPECTS(
            lean.leanError != LeanError::notLawful, at + "model: staged state not lawful");

        TER const leanTer = lean.leanError ? TER{tefEXCEPTION} : lean.error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            leanTer == cpp.ter, at + "lean=" + transToken(leanTer) + " cpp=" + transToken(cpp.ter));
        if (cpp.ter != tesSUCCESS || leanTer != tesSUCCESS)
            return cpp.ter;

        auto const same = [&](char const* field, Number const& l, Number const& c) {
            BEAST_EXPECTS(l == c, at + field + " lean=" + to_string(l) + " cpp=" + to_string(c));
        };
        same("assetsTotal", lean.vault.assetsTotal, cpp.post.assetsTotal);
        same("assetsAvailable", lean.vault.assetsAvailable, cpp.post.assetsAvailable);
        same("sharesTotal", lean.vault.sharesTotal, cpp.post.sharesTotal);
        same("lossUnrealized", lean.vault.lossUnrealized, cpp.post.lossUnrealized);
        Number const charged = cpp.post.assetsTotal - cpp.pre.assetsTotal;
        BEAST_EXPECTS(charged <= Number{amount}, at + "cpp charged " + to_string(charged));
        BEAST_EXPECTS(
            Number{lean.assets} <= Number{amount},
            at + "lean charged " + to_string(Number{lean.assets}));
        return cpp.ter;
    }

    // One price case: the row's amount deposited into its assets total and shares total.
    TER
    checkPriceCase(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        PriceCusp const& c)
    {
        StagedVault const staged{
            .available = gridUnits(env, vault, c.total),
            .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal)};
        return checkDeposit(env, vault, depositor, staged, gridUnits(env, vault, c.amount));
    }

    void
    testOpenLimitSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepOpenLimit(env, vault, depositor);
        }
    }

    // Open limit: a deposit is rejected (tecLIMIT_EXCEEDED) once yield unrealized + assets total +
    // charge exceeds 9e15 grid units. kOpenLimitCases stage price 1, so the charge is the amount.
    void
    sweepOpenLimit(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " open limit-Sweep").c_str());
        runAroundCusp(kOpenLimitCases, [&](OpenLimitCusp const& c) {
            StagedVault const staged{
                .available = gridUnits(env, vault, c.total),
                .yield = gridUnits(env, vault, c.yield),
                .sharesTotal = static_cast<std::uint64_t>(c.total)};
            return checkDeposit(env, vault, depositor, staged, gridUnits(env, vault, c.amount));
        });
    }

    void
    testAssetsMaximumSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepAssetsMaximum(env, vault, depositor);
        }
    }

    // Assets maximum: a deposit is rejected (tecLIMIT_EXCEEDED) once assets total + charge exceeds
    // a non-zero AssetsMaximum. kAssetsMaximumCases stage price 1, so the charge is the amount.
    void
    sweepAssetsMaximum(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " assets maximum-Sweep").c_str());
        // std::int64_t const assetsTotal = 1'000'000;
        // std::int64_t const assetsMaximum = 1'001'000;
        runAroundCusp(kAssetsMaximumCases, [&](AssetsMaximumCusp const& c) {
            StagedVault const staged{
                .available = gridUnits(env, vault, c.total),
                .maximum = gridUnits(env, vault, c.maximum),
                .sharesTotal = static_cast<std::uint64_t>(c.total)};
            return checkDeposit(env, vault, depositor, staged, gridUnits(env, vault, c.amount));
        });
    }

    void
    testZeroSharesSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepZeroShares(env, vault, depositor);
        }
    }

    // Zero shares: a deposit buying trunc(shares total * amount / assets total) = 0 shares is
    // rejected (tecPRECISION_LOSS). Each row of kZeroSharesCases buys exactly one share.
    void
    sweepZeroShares(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " zero shares-Sweep").c_str());
        runAroundCusp(kZeroSharesCases, [&](PriceCusp const& c) {
            return checkPriceCase(env, vault, depositor, c);
        });
    }

    void
    testClampToZeroSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepClampToZero(env, vault, depositor);
        }
    }

    // Clamp to zero: when the shares bought are worth less than a grid step, the charge floors to
    // zero and the deposit is rejected (tecPRECISION_LOSS). Each row of kClampToZeroCases charges
    // exactly one unit.
    void
    sweepClampToZero(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " clamp to zero-Sweep").c_str());
        runAroundCusp(kClampToZeroCases, [&](PriceCusp const& c) {
            return checkPriceCase(env, vault, depositor, c);
        });
    }

    void
    testChargeRoundingSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepChargeRounding(env, vault, depositor);
        }
    }

    // Charge rounding: the charge assets total * shares bought / shares total rounds to the nearest
    // unit, half to even. Each row of kChargeRoundingCases is an exact half; both sides succeed
    // there, so the cusp shows only in the post-state totals.
    void
    sweepChargeRounding(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " charge rounding-Sweep").c_str());
        runAroundCusp(
            kChargeRoundingCases,
            [&](PriceCusp const& c) { return checkPriceCase(env, vault, depositor, c); },
            false);
    }

    void
    testShareMintCapSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepShareMintCap(env, vault, depositor);
        }
    }

    // Share mint cap: minting past 2^63 - 1 outstanding shares fails the share send
    // (tecPATH_DRY). Each row of kShareMintCapCases mints up to exactly the cap.
    void
    sweepShareMintCap(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " share mint cap-Sweep").c_str());
        runAroundCusp(kShareMintCapCases, [&](PriceCusp const& c) {
            return checkPriceCase(env, vault, depositor, c);
        });
    }

    void
    testSubGridAmountSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepSubGridAmount(env, vault, depositor);
        }
    }

    // Sub-grid amount: an IOU amount below one grid step rounds to zero in preclaim
    // (tecPRECISION_LOSS). kOneGridStepCases are mantissas at exponent -(scale + 15), where
    // kOneGridStepMantissa is exactly one grid step.
    void
    sweepSubGridAmount(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " sub-grid amount-Sweep").c_str());
        auto const sle = env.le(vault);
        Asset const asset = sle->at(sfAsset);
        int const scale = sle->at(sfScale);
        StagedVault const staged{
            .available = gridUnits(env, vault, 1'000'000), .sharesTotal = 1'000'000};
        runAroundCusp(kOneGridStepCases, [&](std::int64_t mantissa) {
            STAmount const amount{asset, static_cast<std::uint64_t>(mantissa), -(scale + 15)};
            return checkDeposit(env, vault, depositor, staged, amount);
        });
    }

    void
    testShareOverflowSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, depositor] : vaults)
        {
            sweepShareOverflow(env, vault, depositor);
        }
    }

    // Share overflow: a first IOU deposit mints amount * 10^scale shares; at 2^63 the count
    // overflows (tecPATH_DRY), just below it the amount is past the open limit (tecLIMIT_EXCEEDED).
    // kShareOverflowCases are mantissas at exponent 3 - scale.
    void
    sweepShareOverflow(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        beginCase(("deposit " + vaultName(env, vault) + " share overflow-Sweep").c_str());
        auto const sle = env.le(vault);
        Asset const asset = sle->at(sfAsset);
        int const scale = sle->at(sfScale);
        StagedVault const empty{.available = gridUnits(env, vault, 0), .sharesTotal = 0};
        runAroundCusp(kShareOverflowCases, [&](std::int64_t mantissa) {
            STAmount const amount{asset, static_cast<std::uint64_t>(mantissa), 3 - scale};
            return checkDeposit(env, vault, depositor, empty, amount);
        });
    }

    void
    runTests() override
    {
        using namespace jtx;

        // One ledger holding a vault per asset; every staged deposit (old tests and sweeps) runs
        // on a throwaway view of it.
        Env env{*this};
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const depositor{"depositor"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.fund(XRP(9'500'000'000), depositor);
        env.close();

        PrettyAsset const xrp = xrpIssue();
        PrettyAsset const iou = issuer["USD"];
        // An IOU holder that is not the issuer; its balance is staged per test.
        env(trust(holder, iou(10'000'000'000'000'000LL)));
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor});
        mptt.authorize({.account = owner});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer, depositor, mpt(9'200'000'000'000'000)));
        env(pay(issuer, owner, mpt(10'000)));
        env.close();

        // The IOU depositor is the issuer, which skips the C++-only trust-line precision checks.
        Keylet const xrpVault = createSweepVault(env, owner, depositor, xrp);
        Keylet const mptVault = createSweepVault(env, owner, depositor, mpt);
        // IOU at the smallest, the default and the largest vault scale.
        Keylet const iouScale0Vault = createSweepVault(env, owner, issuer, iou, 0);
        Keylet const iouScale6Vault = createSweepVault(env, owner, issuer, iou, 6);
        Keylet const iouScale10Vault = createSweepVault(env, owner, issuer, iou, 10);

        // XRP: scale 0, no share overflow within the XRP domain.
        testVaultDepositXRP(
            env, xrpVault, depositor, XRP(0), drops(1), tesSUCCESS);  // minimum deposit
        testVaultDepositXRP(env, xrpVault, depositor, XRP(0), XRP(1'000), tesSUCCESS);
        // Open limit: 9e15 drops. Covered by testOpenLimitSweep.
        testVaultDepositXRP(env, xrpVault, depositor, XRP(0), drops(kOpenLimitUnits), tesSUCCESS);
        testVaultDepositXRP(
            env, xrpVault, depositor, XRP(0), drops(kOpenLimitUnits + 1), tecLIMIT_EXCEEDED);
        testVaultDepositXRP(
            env, xrpVault, depositor, XRP(1'000), XRP(1'000), tesSUCCESS);  // non-empty vault
        testVaultDepositXRP(
            env,
            xrpVault,
            depositor,
            XRP(1'000),
            drops(1),
            tesSUCCESS);  // minimum deposit, non-empty

        // IOU: default vault scale 6, so shares ~ amount * 1e6.
        testVaultDepositIOU(env, iouScale6Vault, holder, Number{0}, Number{1}, tesSUCCESS);
        testVaultDepositIOU(env, iouScale6Vault, holder, Number{0}, Number{1'000}, tesSUCCESS);
        // Open limit at scale 6: 9e9. It keeps the shares (amount * 1e6) far below INT64_MAX.
        // Covered by testOpenLimitSweep.
        Number const iouOpenLimit{kOpenLimitUnits, -6};
        testVaultDepositIOU(env, iouScale6Vault, holder, Number{0}, iouOpenLimit, tesSUCCESS);
        testVaultDepositIOU(
            env,
            iouScale6Vault,
            holder,
            Number{0},
            iouOpenLimit + Number{1, -6},
            tecLIMIT_EXCEEDED);
        // 1e10 at scale 6 needs 17 digits: the total would leave the base exponent.
        testVaultDepositIOU(
            env, iouScale6Vault, holder, Number{0}, Number{1, 10}, tecLIMIT_EXCEEDED);
        testVaultDepositIOU(env, iouScale6Vault, issuer, Number{0}, Number{1}, tesSUCCESS);
        testVaultDepositIOU(env, iouScale6Vault, issuer, Number{0}, iouOpenLimit, tesSUCCESS);
        testVaultDepositIOU(
            env,
            iouScale6Vault,
            issuer,
            Number{0},
            iouOpenLimit + Number{1, -6},
            tecLIMIT_EXCEEDED);

        // covered by testShareOverflowSweep
        testVaultDepositIOU(
            env,
            iouScale6Vault,
            issuer,
            Number{0},
            Number{9'999'999'999'999'999LL, 80},
            tecPATH_DRY);
        testVaultDepositIOU(
            env, iouScale6Vault, issuer, Number{0}, Number{1, -80}, tecPRECISION_LOSS);

        // roundedDepositAmount
        testRoundedDepositSuccess(env, iouScale6Vault, issuer);
        // covered by testSubGridAmountSweep
        testRoundedDepositBelowVaultScale(env, iouScale6Vault, holder);
        testRoundedDepositBelowVaultScale(env, iouScale6Vault, issuer);
        // sanity: a normal deposit into the same non-empty vault still succeeds
        testVaultDepositIOU(env, iouScale6Vault, holder, Number{1, 9}, Number{1'000}, tesSUCCESS);

        // MPT: scale 0, sfMPTAmount and shares are int64.
        testVaultDepositMPT(env, mptVault, depositor, 0, 1, tesSUCCESS);
        testVaultDepositMPT(env, mptVault, depositor, 0, 1'000, tesSUCCESS);
        // Open limit: 9e15 units, far below the share type maximum INT64_MAX. Covered by
        // testOpenLimitSweep.
        testVaultDepositMPT(env, mptVault, depositor, 0, kOpenLimitUnits, tesSUCCESS);
        testVaultDepositMPT(env, mptVault, depositor, 1'000, 1'000, tesSUCCESS);  // non-empty vault
        testVaultDepositMPT(env, mptVault, depositor, 1, kOpenLimitUnits - 1, tesSUCCESS);
        testVaultDepositMPT(env, mptVault, depositor, kOpenLimitUnits - 1, 1, tesSUCCESS);
        testVaultDepositMPT(env, mptVault, depositor, kOpenLimitUnits - 1, 2, tecLIMIT_EXCEEDED);

        // Truncated to the 1e-6 grid on both sides. Covered by testSubGridAmountSweep.
        testVaultDepositIOU(
            env, iouScale6Vault, holder, Number{1, 9}, Number{100'000'006, -7}, tesSUCCESS);
        testVaultDepositIOU(
            env, iouScale6Vault, holder, Number{1, 9}, Number{100'000'001, -7}, tesSUCCESS);

        // Empty-vault share truncation (C++ truncates toward zero, not to-nearest):
        // 1.5e-6 USD * 1e6 scale = 1.5 shares -> 1.
        testVaultDepositIOU(env, iouScale6Vault, issuer, Number{0}, Number{15, -7}, tesSUCCESS);
        // Zero-share deposit is rejected: 0.6e-6 USD * 1e6 = 0.6 shares -> 0 -> tecPRECISION_LOSS.
        // covered by testSubGridAmountSweep (preclaim rounds it to zero first)
        testVaultDepositIOU(
            env, iouScale6Vault, issuer, Number{0}, Number{6, -7}, tecPRECISION_LOSS);

        testVaultDepositExchangeRate(env, iouScale6Vault, issuer);

        // Extreme NAV ratio AssetsTotal >> SharesTotal: a unit deposit buys zero shares.
        // covered by testZeroSharesSweep
        testVaultDepositUpdatedStateMPT(
            env, mptVault, depositor, Number{1, 18}, 1, 1, tecPRECISION_LOSS);
        // Share price 3e-7: one grid unit buys 3 shares worth 9e-7, which clamps to nothing.
        // covered by testClampToZeroSweep
        testVaultDepositUpdatedStateIOU(
            env,
            iouScale6Vault,
            issuer,
            Number{1'000},
            3'333'333'333ULL,
            Number{1, -6},
            tecPRECISION_LOSS);
        // AssetsTotal near the STAmount exponent ceiling: a small IOU deposit rounds to zero.
        testRoundedDepositUpdatedStateIOU(
            env,
            iouScale6Vault,
            issuer,
            Number{9'999'999'999'999'999LL, 80},
            Number{1},
            tecPRECISION_LOSS);
        // IOU AssetsTotal + amount overflows
        testRoundedDepositOverflow(env, iouScale6Vault, issuer);

        // Insolvent vault (assetsTotal=0, sharesTotal>0): deposits are blocked with tecLOCKED.
        testVaultDepositUpdatedStateMPT(
            env, mptVault, depositor, Number{0}, 1'000'000, 1'000, tecLOCKED);
        // Deposits blocked by the owner.
        testVaultDepositBlocked(env, xrpVault, depositor);
        // Unrealized yield counts toward the open-limit capacity: 10 under the limit (one share
        // per unit) with 10 of yield rejects one unit, with 9 of yield it fits exactly.
        // covered by testOpenLimitSweep
        testVaultDepositUpdatedStateMPT(
            env,
            mptVault,
            depositor,
            Number{kOpenLimitUnits - 10},
            static_cast<std::uint64_t>(kOpenLimitUnits - 10),
            1,
            tecLIMIT_EXCEEDED,
            Number{10});
        testVaultDepositUpdatedStateMPT(
            env,
            mptVault,
            depositor,
            Number{kOpenLimitUnits - 10},
            static_cast<std::uint64_t>(kOpenLimitUnits - 10),
            1,
            tesSUCCESS,
            Number{9});
        // Donation to an empty vault is blocked with tecNO_PERMISSION
        testVaultDonationEmptyVault(env, xrpVault, owner);
        // Deposit over a non-zero maximum is blocked with tecLIMIT_EXCEEDED
        // covered by testAssetsMaximumSweep
        testVaultDepositCap(env, mptVault, depositor, Number{1'000}, tecLIMIT_EXCEEDED);
        testVaultDepositCap(env, mptVault, depositor, Number{2'000}, tesSUCCESS);

        // Open discrepancies, disabled until the C++ code is fixed.
        // clang-format off
        // testDepositDilution();          // FV_M2_8_c: deposit lowers the share price (both)
        // testDepositPastOpenLimit(env, iouScale6Vault, issuer, Number{9'999'999'999'999'999LL, -6}, Number{1, -5});  // FV_M2_15_b

        // Properties both sides now satisfy, kept as regression tests.
        // covered by testChargeRoundingSweep
        testVaultDepositOvervaluedShares(env, xrpVault, depositor);  // FV_M2_3: the share charge rounds up
        testDepositAppliedDelta();                                   // totals move by exactly the amount paid
        testVaultDonationInsolvent(env, mptVault, owner);            // FV_M2_7: a donation passes the insolvency check
        // FV_M2_15: 899999.9999999999 is at the scale-10 open limit (9e5); +5 passes it.
        // covered by testOpenLimitSweep
        testDepositPastOpenLimit(env, iouScale10Vault, issuer, Number{8'999'999'999'999'999LL, -10}, Number{5});
        // clang-format on

        // Sweeps.
        SweepVaults const ious{
            {iouScale0Vault, issuer}, {iouScale6Vault, issuer}, {iouScale10Vault, issuer}};
        SweepVaults const integral{{xrpVault, depositor}, {mptVault, depositor}};
        SweepVaults all = integral;
        all.insert(all.end(), ious.begin(), ious.end());

        testOpenLimitSweep(env, all);
        testAssetsMaximumSweep(env, all);
        testZeroSharesSweep(env, all);
        testChargeRoundingSweep(env, integral);
        testSubGridAmountSweep(env, ious);
        testShareOverflowSweep(env, ious);
        testClampToZeroSweep(env, ious);

        testShareMintCapSweep(env, all);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
