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
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

struct DepositCase
{
    StagedVault vault;
    std::int64_t amount;
    TER expected;
    int exponent{};
    bool donate{};
};

class LeanVaultDeposit_test : public LeanSuite
{
    // Every test runs on one shared ledger: each stages its vault on a throwaway view (seed
    // deposits become the shares a first deposit mints) and expects its verdict on both sides,
    // with every vault field equal when both succeed. The boundary tests do this for explicit
    // case lists.
    // Staged states may be unreachable by any transaction: a verdict compares model and C++ on the
    // same pre-state and does not claim the state is reachable (see stageVault).

    // A seed deposit of `seed` into an empty vault: the vault holds it and has minted seed *
    // 10^scale shares.
    static StagedAmounts
    seededVault(jtx::Env& env, Keylet const& vault, STAmount const& seed)
    {
        int const scale = env.le(vault)->at(sfScale);
        Number const shares = Number{seed} * Number{1, scale};
        return StagedAmounts{
            .available = seed,
            .sharesTotal = static_cast<std::uint64_t>(static_cast<std::int64_t>(shares)),
        };
    }

    // A holder other than the asset's issuer holds exactly the amount it deposits.
    static StagedAmounts
    fundDepositor(StagedAmounts staged, jtx::Account const& depositor, STAmount const& amount)
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
        StagedAmounts const& staged,
        STAmount const& amount,
        TER expected,
        bool donate = false)
    {
        AppliedVaultTx const cpp = applyDeposit(env, vault, depositor, staged, amount, donate);
        LeanVaultResult const lean =
            leanVaultDeposit(cpp.pre, amount, donate, parentCloseTime(env));
        std::string const at = sampleText(staged, amount);
        expectSame(*this, at, cpp, lean, expected);
        if (cpp.ter != tesSUCCESS || lean.leanError || lean.error || !cpp.assets)
            return;
        BEAST_EXPECTS(*cpp.assets <= Number{amount}, at + "cpp charged " + to_string(*cpp.assets));
        BEAST_EXPECTS(
            Number{lean.assets} <= Number{amount},
            at + "lean charged " + to_string(Number{lean.assets}));
    }

    // Model of preclaim: leanRoundedDepositAmount rounds to the vault scale and returns exactly
    // one of the rounded amount (success) or an error TER, or the model error `leanError` where
    // C++ throws (tefEXCEPTION); C++ runs the whole deposit.
    void
    expectRoundedDeposit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        StagedAmounts const& staged,
        STAmount const& amount,
        TER expected,
        std::optional<LeanError> leanError = std::nullopt)
    {
        AppliedVaultTx const cpp = applyDeposit(env, vault, depositor, staged, amount);
        LeanAmountResult const rounded = leanRoundedDepositAmount(cpp.pre, amount);
        expectLawful(rounded);
        BEAST_EXPECTS(
            cpp.ter == expected,
            std::string("cpp=") + transToken(cpp.ter) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            rounded.leanError == leanError,
            "lean error " + leanErrorText(rounded.leanError) + " expected " +
                leanErrorText(leanError));

        std::optional<TER> const expectedError =
            expected == tesSUCCESS || leanError ? std::nullopt : std::optional<TER>{expected};
        std::optional<TER> const& leanTer = rounded.error;
        // The model result carries no asset, so compare the rounded value (a Number), not the
        // STAmount (whose operator== also checks currency).
        std::optional<Number> const leanAmount = rounded.amount
            ? std::optional<Number>{static_cast<Number>(*rounded.amount)}
            : std::nullopt;
        std::optional<Number> const expectedAmount = expected == tesSUCCESS
            ? std::optional<Number>{static_cast<Number>(amount)}
            : std::nullopt;
        BEAST_EXPECTS(
            leanTer == expectedError,
            std::string("error lean=") + (leanTer ? transToken(*leanTer) : "none") + " expected " +
                (expectedError ? transToken(*expectedError) : "none"));
        BEAST_EXPECTS(
            leanAmount == expectedAmount,
            std::string("amount lean=") + (leanAmount ? to_string(*leanAmount) : "none") +
                " expected " + (expectedAmount ? to_string(*expectedAmount) : "none"));
    }

    // XRP: scale 0, no share overflow within the XRP domain.
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

    // IOU: default vault scale 6, so shares ~ amount * 1e6.
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
        StagedAmounts const staged = fundDepositor(
            seededVault(env, vault, STAmount{asset, vaultBalanceBeforeDeposit}), depositor, a);
        expectStagedDeposit(env, vault, depositor, staged, a, expected);
    }

    // MPT: scale 0, sfMPTAmount and shares are int64.
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
            seededVault(env, vault, vaultUnits(env, vault, vaultBalanceBeforeDeposit)),
            vaultUnits(env, vault, amount),
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
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, Number{1}});
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
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .yield = STAmount{asset, yieldUnrealized},
            .sharesTotal = sharesTotal,
        };
        expectStagedDeposit(
            env, vault, depositor, staged, vaultUnits(env, vault, amount), expected);
    }

    // The owner blocked deposits (VaultSet), so a deposit is tecLOCKED on both sides.
    void
    testVaultDepositBlocked(jtx::Env& env, Keylet const& vault, jtx::Account const& depositor)
    {
        testcase("deposit into a vault with deposits blocked");
        StagedAmounts staged = seededVault(env, vault, vaultUnits(env, vault, 1'000'000'000));
        staged.depositBlocked = true;
        expectStagedDeposit(
            env, vault, depositor, staged, vaultUnits(env, vault, 100'000'000), tecLOCKED);
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
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = sharesTotal,
        };
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
        TER expected,
        std::optional<LeanError> leanError = std::nullopt)
    {
        testcase(
            "updated-state IOU rounded deposit " + to_string(amount) +
            " (assetsTotal=" + to_string(assetsTotal) + ")");
        Asset const asset = env.le(vault)->at(sfAsset);
        // Shares so the vault is not zero-sized, the deposit still rejects on rounding.
        StagedAmounts const staged{
            .available = STAmount{asset, assetsTotal},
            .sharesTotal = 1'000'000,
        };
        expectRoundedDeposit(
            env, vault, issuer, staged, STAmount{asset, amount}, expected, leanError);
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

    // A deposit below the vault's 1e-6 grid: preclaim rounds it to zero. Covered by
    // testDepositBoundaries.
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

    // AssetsTotal + amount near the IOU maximum overflows: C++ throws, the model returns overflow.
    void
    testRoundedDepositOverflow(jtx::Env& env, Keylet const& vault, jtx::Account const& issuer)
    {
        testRoundedDepositUpdatedStateIOU(
            env,
            vault,
            issuer,
            Number{9'999'999'999'999'999LL, 80},
            Number{9'999'999'999'999'999LL, 80},
            tefEXCEPTION,
            LeanError::overflow);
    }

    // FV_M2_3 (pins the C++ behaviour): the charge rounds to nearest, so a deposit can pay less
    // than its shares are worth, diluting existing holders; the model rounds the same way.
    // Covered by the charge rounding cases of testDepositBoundaries.
    void
    testVaultDepositOvervaluedShares(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor)
    {
        testcase("deposit overvalued shares");
        // A 3-drop seed and a 2-drop donation: 1 share = 1.667 drops. A 4-drop deposit buys 2
        // shares worth 3.33 drops; both sides charge round(3.33) = 3.
        StagedAmounts staged = seededVault(env, vault, vaultUnits(env, vault, 3));
        staged.available = vaultUnits(env, vault, 5);
        expectStagedDeposit(env, vault, depositor, staged, vaultUnits(env, vault, 4), tesSUCCESS);
    }

    // Donating to a vault with no outstanding shares is rejected (tecNO_PERMISSION).
    void
    testVaultDonationEmptyVault(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        testcase("donation to empty vault");
        StagedAmounts const empty{.available = vaultUnits(env, vault, 0), .sharesTotal = 0};
        expectStagedDeposit(
            env, vault, owner, empty, vaultUnits(env, vault, 100'000'000), tecNO_PERMISSION, true);
    }

    // A deposit of 1000 into a vault holding 1000 under the AssetsMaximum `cap`: rejected with
    // tecLIMIT_EXCEEDED when the total would pass a non-zero cap (a zero maximum means unlimited).
    // Covered by testDepositBoundaries.
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
        StagedAmounts const staged{
            .available = vaultUnits(env, vault, 1'000),
            .maximum = STAmount{asset, cap},
            .sharesTotal = 1'000,
        };
        expectStagedDeposit(env, vault, depositor, staged, vaultUnits(env, vault, 1'000), expected);
    }

    // FV_M2_7: a donation to an insolvent vault (assetsTotal=0, sharesTotal>0) is NOT blocked
    void
    testVaultDonationInsolvent(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        testcase("donation to insolvent vault");
        StagedAmounts const insolvent{
            .available = vaultUnits(env, vault, 0),
            .sharesTotal = 1'000'000,
        };
        expectStagedDeposit(
            env, vault, owner, insolvent, vaultUnits(env, vault, 1'000), tesSUCCESS, true);
    }

    // FV_M2_8 (both sides): the sfAssetsTotal += update re-rounds, dropping the sum's low
    // digits and lowering the share price. Assert the price does not fall.
    void
    testDepositDilution()
    {
        using namespace jtx;
        testcase("deposit lowers the share price (dilution)");

        Env env{*this, vaultTestAmendments()};
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

        Env env{*this, vaultTestAmendments()};
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

    // The vaults a case list runs on, each with the account that deposits into it.
    using TestVaults = std::vector<std::pair<Keylet, jtx::Account>>;

    // What every test runs on: the accounts and a vault per asset. Every staged deposit runs on a
    // throwaway view of this one ledger.
    struct Setup
    {
        jtx::Account owner;
        jtx::Account issuer;
        jtx::Account depositor;
        // An IOU holder that is not the issuer; its balance is staged per test.
        jtx::Account holder;
        Keylet xrpVault;
        Keylet mptVault;
        Keylet iouDefaultScaleVault;
        Keylet iouMaxScaleVault;
        TestVaults ious;
        TestVaults integral;
        TestVaults all;
        // The default-scale IOU vault with the holder as depositor.
        TestVaults iouHolder;
    };

    static Setup
    setup(jtx::Env& env)
    {
        using namespace jtx;
        using namespace std::chrono_literals;

        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const depositor{"depositor"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.fund(XRP(9'500'000'000), depositor);
        env.close();
        // Staged dates reach far before the parent close time, which starts near 0.
        env.close(env.now() + 1'000'000'000s);

        PrettyAsset const xrp = xrpIssue();
        PrettyAsset const iou = issuer["USD"];
        env(trust(holder, iou(10'000'000'000'000'000LL)));
        // The owner donates IOU in the closed-ended matrix and the donation tables.
        env(trust(owner, iou(Number{1, 10})));
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor});
        mptt.authorize({.account = owner});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer, depositor, mpt(9'200'000'000'000'000)));
        env(pay(issuer, owner, mpt(10'000)));
        env.close();

        // The IOU depositor is the issuer. The model takes no depositor balance, so the
        // depositor-side checks (insufficient funds, trust-line precision) are outside it and the
        // tables do not stage them.
        Keylet const xrpVault = createVault(env, owner, xrp);
        Keylet const mptVault = createVault(env, owner, mpt);
        // IOU at the smallest, the default and the largest vault scale.
        Keylet const iouMinScaleVault = createVault(env, owner, iou, kVaultMinimumIouScale);
        Keylet const iouDefaultScaleVault = createVault(env, owner, iou, kVaultDefaultIouScale);
        Keylet const iouMaxScaleVault =
            createVault(env, owner, iou, kFixedPrecisionVaultMaximumIouScale);
        TestVaults const ious{
            {iouMinScaleVault, issuer},
            {iouDefaultScaleVault, issuer},
            {iouMaxScaleVault, issuer},
        };
        TestVaults const integral{{xrpVault, depositor}, {mptVault, depositor}};
        TestVaults all = integral;
        all.insert(all.end(), ious.begin(), ious.end());
        // One unit each: the holder gets its share MPToken and an IOU vault its pseudo-account
        // trust line, which staging state on the vault needs.
        for (auto const& [vault, account] : all)
        {
            env(jtx::Vault::deposit(
                {.depositor = account, .id = vault.key, .amount = vaultUnits(env, vault, 1)}));
        }
        env.close();
        // The holder's share MPToken, staged by the closed-ended matrix; its IOU balance is back
        // to zero.
        STAmount const unit = vaultUnits(env, iouDefaultScaleVault, 1);
        env(pay(issuer, holder, unit));
        env.close();
        env(jtx::Vault::deposit(
            {.depositor = holder, .id = iouDefaultScaleVault.key, .amount = unit}));
        env.close();
        return {
            .owner = owner,
            .issuer = issuer,
            .depositor = depositor,
            .holder = holder,
            .xrpVault = xrpVault,
            .mptVault = mptVault,
            .iouDefaultScaleVault = iouDefaultScaleVault,
            .iouMaxScaleVault = iouMaxScaleVault,
            .ious = ious,
            .integral = integral,
            .all = all,
            .iouHolder = {{iouDefaultScaleVault, holder}},
        };
    }

    // Each case stages its vault, deposits `amount` * 10^`exponent` units and expects its verdict
    // on both sides. Rows are grouped by the cusp they sit around.
    // - Open limit: a deposit is rejected (tecLIMIT_EXCEEDED) once yield unrealized + assets
    //   total + charge exceeds 9e15 grid units.
    // - Assets maximum: a deposit is rejected (tecLIMIT_EXCEEDED) once assets total + charge
    //   exceeds a non-zero AssetsMaximum. The rows stage price 1, so the charge is the amount.
    // - Zero shares: a deposit buying trunc(shares total * amount / assets total) = 0 shares is
    //   rejected (tecPRECISION_LOSS). Each cusp buys exactly one share.
    // - Charge rounding: the charge assets total * shares bought / shares total rounds to the
    //   nearest unit, half to even. Each cusp is an exact half and succeeds, so it shows only in
    //   the post-state totals.
    // - Charge rounding verdict: an assets maximum turns the half-to-even charge into the
    //   verdict; half up or flooring would flip it.
    // - Clamp to zero: when the shares bought are worth less than a grid step, the charge floors to
    //   zero and the deposit is rejected (tecPRECISION_LOSS). Each cusp charges exactly one unit.
    // - Share mint cap: minting past 2^63 - 1 outstanding shares fails the share send
    //   (tecPATH_DRY). Each cusp mints up to exactly the cap.
    // - Sub-grid amount: an IOU amount below one grid step rounds to zero in preclaim
    //   (tecPRECISION_LOSS). Mantissa 10^15 at exponent -15 is exactly one grid step.
    // - Share overflow: a first IOU deposit mints amount * 10^scale shares; at 2^63 the count
    //   overflows (tecPATH_DRY), just below it the amount is past the open limit
    //   (tecLIMIT_EXCEEDED).
    // - Donation: the owner's donation mints no shares but meets the open limit, the assets
    //   maximum, the grid and the deposit block like a deposit. It needs shares outstanding
    //   (tecNO_PERMISSION) and may refill an insolvent vault.
    // - Loss ignored: the price is assets total over shares total; the unrealized loss does not
    //   lower it.
    // - Locked: a plain deposit into a blocked or insolvent vault is rejected (tecLOCKED).
    // - First deposit: a deposit into an empty vault mints amount * 10^scale shares.
    // clang-format off
    static constexpr DepositCase kOpenLimit[] = {
        // yield 0, total 1, amount 8'999'999'999'999'999
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 8'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 8'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 8'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 8'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 8'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 8'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 9'000'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 9'000'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        // yield 0, total 8'999'999'999'999'999, amount 1
        {.vault = {.available = 8'999'999'999'999'997, .sharesTotal = 8'999'999'999'999'997}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'999'999'999'997, .sharesTotal = 8'999'999'999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'999'999'999'997, .sharesTotal = 8'999'999'999'999'997}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'999'999'999'998, .sharesTotal = 8'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'999'999'999'998, .sharesTotal = 8'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'999'999'999'998, .sharesTotal = 8'999'999'999'999'998}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'999'999'999, .sharesTotal = 8'999'999'999'999'999}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'999'999'999'999, .sharesTotal = 8'999'999'999'999'999}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'999'999'999, .sharesTotal = 8'999'999'999'999'999}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'000'000'000'000'000, .sharesTotal = 9'000'000'000'000'000}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'000'000'000'000'000, .sharesTotal = 9'000'000'000'000'000}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'000'000'000'000'000, .sharesTotal = 9'000'000'000'000'000}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'000'000'000'000'001, .sharesTotal = 9'000'000'000'000'001}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'000'000'000'000'001, .sharesTotal = 9'000'000'000'000'001}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'000'000'000'000'001, .sharesTotal = 9'000'000'000'000'001}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        // yield 0, total 4'500'000'000'000'000, amount 4'500'000'000'000'000
        {.vault = {.available = 4'499'999'999'999'998, .sharesTotal = 4'499'999'999'999'998}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'998, .sharesTotal = 4'499'999'999'999'998}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'998, .sharesTotal = 4'499'999'999'999'998}, .amount = 4'500'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'998, .sharesTotal = 4'499'999'999'999'998}, .amount = 4'500'000'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'998, .sharesTotal = 4'499'999'999'999'998}, .amount = 4'500'000'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'999, .sharesTotal = 4'499'999'999'999'999}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'999, .sharesTotal = 4'499'999'999'999'999}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'999, .sharesTotal = 4'499'999'999'999'999}, .amount = 4'500'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'999, .sharesTotal = 4'499'999'999'999'999}, .amount = 4'500'000'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 4'499'999'999'999'999, .sharesTotal = 4'499'999'999'999'999}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'000, .sharesTotal = 4'500'000'000'000'000}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'500'000'000'000'000, .sharesTotal = 4'500'000'000'000'000}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'500'000'000'000'000, .sharesTotal = 4'500'000'000'000'000}, .amount = 4'500'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 4'500'000'000'000'000, .sharesTotal = 4'500'000'000'000'000}, .amount = 4'500'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'000, .sharesTotal = 4'500'000'000'000'000}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'001, .sharesTotal = 4'500'000'000'000'001}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'500'000'000'000'001, .sharesTotal = 4'500'000'000'000'001}, .amount = 4'499'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'500'000'000'000'001, .sharesTotal = 4'500'000'000'000'001}, .amount = 4'500'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'001, .sharesTotal = 4'500'000'000'000'001}, .amount = 4'500'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'001, .sharesTotal = 4'500'000'000'000'001}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'002, .sharesTotal = 4'500'000'000'000'002}, .amount = 4'499'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'500'000'000'000'002, .sharesTotal = 4'500'000'000'000'002}, .amount = 4'499'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'002, .sharesTotal = 4'500'000'000'000'002}, .amount = 4'500'000'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'002, .sharesTotal = 4'500'000'000'000'002}, .amount = 4'500'000'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'500'000'000'000'002, .sharesTotal = 4'500'000'000'000'002}, .amount = 4'500'000'000'000'002, .expected = tecLIMIT_EXCEEDED},
        // yield 1'000'000'000, total 1, amount 8'999'998'999'999'999
        {.vault = {.available = 1, .yield = 1'000'000'000, .sharesTotal = 1}, .amount = 8'999'998'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 1, .yield = 1'000'000'000, .sharesTotal = 1}, .amount = 8'999'998'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1, .yield = 1'000'000'000, .sharesTotal = 1}, .amount = 8'999'998'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1, .yield = 1'000'000'000, .sharesTotal = 1}, .amount = 8'999'999'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .yield = 1'000'000'000, .sharesTotal = 1}, .amount = 8'999'999'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .yield = 1'000'000'000, .sharesTotal = 2}, .amount = 8'999'998'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 2, .yield = 1'000'000'000, .sharesTotal = 2}, .amount = 8'999'998'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2, .yield = 1'000'000'000, .sharesTotal = 2}, .amount = 8'999'998'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .yield = 1'000'000'000, .sharesTotal = 2}, .amount = 8'999'999'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .yield = 1'000'000'000, .sharesTotal = 2}, .amount = 8'999'999'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .yield = 1'000'000'000, .sharesTotal = 3}, .amount = 8'999'998'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 3, .yield = 1'000'000'000, .sharesTotal = 3}, .amount = 8'999'998'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .yield = 1'000'000'000, .sharesTotal = 3}, .amount = 8'999'998'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .yield = 1'000'000'000, .sharesTotal = 3}, .amount = 8'999'999'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .yield = 1'000'000'000, .sharesTotal = 3}, .amount = 8'999'999'000'000'001, .expected = tecLIMIT_EXCEEDED},
        // yield 1'000'000'000, total 8'999'998'999'999'999, amount 1
        {.vault = {.available = 8'999'998'999'999'997, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'997}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'998'999'999'997, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'998'999'999'997, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'997}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'998'999'999'998, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'998'999'999'998, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'998'999'999'998, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'998}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'998'999'999'999, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'999}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'999'998'999'999'999, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'999}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'998'999'999'999, .yield = 1'000'000'000, .sharesTotal = 8'999'998'999'999'999}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'000'000'000, .yield = 1'000'000'000, .sharesTotal = 8'999'999'000'000'000}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'000'000'000, .yield = 1'000'000'000, .sharesTotal = 8'999'999'000'000'000}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'000'000'000, .yield = 1'000'000'000, .sharesTotal = 8'999'999'000'000'000}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'000'000'001, .yield = 1'000'000'000, .sharesTotal = 8'999'999'000'000'001}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'000'000'001, .yield = 1'000'000'000, .sharesTotal = 8'999'999'000'000'001}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 8'999'999'000'000'001, .yield = 1'000'000'000, .sharesTotal = 8'999'999'000'000'001}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        // yield 8'999'999'999'999'998, total 1, amount 1
        {.vault = {.available = 1, .yield = 8'999'999'999'999'998, .sharesTotal = 1}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .yield = 8'999'999'999'999'998, .sharesTotal = 1}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .yield = 8'999'999'999'999'998, .sharesTotal = 1}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .yield = 8'999'999'999'999'998, .sharesTotal = 2}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .yield = 8'999'999'999'999'998, .sharesTotal = 2}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .yield = 8'999'999'999'999'998, .sharesTotal = 2}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .yield = 8'999'999'999'999'998, .sharesTotal = 3}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .yield = 8'999'999'999'999'998, .sharesTotal = 3}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .yield = 8'999'999'999'999'998, .sharesTotal = 3}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr DepositCase kAssetsMaximum[] = {
        // maximum 2, total 1, amount 1
        {.vault = {.available = 1, .maximum = 2, .sharesTotal = 1}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .maximum = 2, .sharesTotal = 1}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .maximum = 2, .sharesTotal = 1}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .maximum = 2, .sharesTotal = 2}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .maximum = 2, .sharesTotal = 2}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .maximum = 2, .sharesTotal = 2}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        // maximum 1'000'000'000, total 1, amount 999'999'999
        {.vault = {.available = 1, .maximum = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 1, .maximum = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1, .maximum = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1, .maximum = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .maximum = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .maximum = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 2, .maximum = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 2, .maximum = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .maximum = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .maximum = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .maximum = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 3, .maximum = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .maximum = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .maximum = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .maximum = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        // maximum 1'000'000'000, total 999'999'999, amount 1
        {.vault = {.available = 999'999'997, .maximum = 1'000'000'000, .sharesTotal = 999'999'997}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'997, .maximum = 1'000'000'000, .sharesTotal = 999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'997, .maximum = 1'000'000'000, .sharesTotal = 999'999'997}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .maximum = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .maximum = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .maximum = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'999, .maximum = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .maximum = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'999, .maximum = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'000, .maximum = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'000, .maximum = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'000, .maximum = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 3, .expected = tecLIMIT_EXCEEDED},
        // maximum 1'000'000'000, total 500'000'000, amount 500'000'000
        {.vault = {.available = 499'999'998, .maximum = 1'000'000'000, .sharesTotal = 499'999'998}, .amount = 499'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'998, .maximum = 1'000'000'000, .sharesTotal = 499'999'998}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'998, .maximum = 1'000'000'000, .sharesTotal = 499'999'998}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'998, .maximum = 1'000'000'000, .sharesTotal = 499'999'998}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'998, .maximum = 1'000'000'000, .sharesTotal = 499'999'998}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .maximum = 1'000'000'000, .sharesTotal = 499'999'999}, .amount = 499'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .maximum = 1'000'000'000, .sharesTotal = 499'999'999}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .maximum = 1'000'000'000, .sharesTotal = 499'999'999}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .maximum = 1'000'000'000, .sharesTotal = 499'999'999}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .maximum = 1'000'000'000, .sharesTotal = 499'999'999}, .amount = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'000, .maximum = 1'000'000'000, .sharesTotal = 500'000'000}, .amount = 499'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .maximum = 1'000'000'000, .sharesTotal = 500'000'000}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .maximum = 1'000'000'000, .sharesTotal = 500'000'000}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .maximum = 1'000'000'000, .sharesTotal = 500'000'000}, .amount = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'000, .maximum = 1'000'000'000, .sharesTotal = 500'000'000}, .amount = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'001, .maximum = 1'000'000'000, .sharesTotal = 500'000'001}, .amount = 499'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'001, .maximum = 1'000'000'000, .sharesTotal = 500'000'001}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'001, .maximum = 1'000'000'000, .sharesTotal = 500'000'001}, .amount = 500'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'001, .maximum = 1'000'000'000, .sharesTotal = 500'000'001}, .amount = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'001, .maximum = 1'000'000'000, .sharesTotal = 500'000'001}, .amount = 500'000'002, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'002, .maximum = 1'000'000'000, .sharesTotal = 500'000'002}, .amount = 499'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'002, .maximum = 1'000'000'000, .sharesTotal = 500'000'002}, .amount = 499'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'002, .maximum = 1'000'000'000, .sharesTotal = 500'000'002}, .amount = 500'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'002, .maximum = 1'000'000'000, .sharesTotal = 500'000'002}, .amount = 500'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'002, .maximum = 1'000'000'000, .sharesTotal = 500'000'002}, .amount = 500'000'002, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr DepositCase kZeroShares[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 4, .expected = tesSUCCESS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1, amount 1'000'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 31'250, amount 32'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 31'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 32'000, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 32'001, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'248}, .amount = 32'002, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 31'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 32'000, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 32'001, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'249}, .amount = 32'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 31'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 32'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 32'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'250}, .amount = 32'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 31'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 31'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 32'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 32'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'251}, .amount = 32'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 31'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 31'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 32'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 32'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 31'252}, .amount = 32'002, .expected = tesSUCCESS},
    };
    static constexpr DepositCase kZeroSharesIntegral[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tesSUCCESS},
    };
    static constexpr DepositCase kZeroSharesIou[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
    };
    // FV_M2_3 (C++ behaviour pinned as expected): the charge rounds to nearest.
    static constexpr DepositCase kChargeRounding[] = {
        // total 3, sharesTotal 2, amount 2
        {.vault = {.available = 3, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 3, .sharesTotal = 1}, .amount = 2, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 3, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 1}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 4, .expected = tesSUCCESS},
        // total 3, sharesTotal 4, amount 2
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 2}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 4}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 5}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 5}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 5}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 5}, .amount = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 6}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 6}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 6}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 6}, .amount = 4, .expected = tesSUCCESS},
        // total 1'000'000'001, sharesTotal 2, amount 500'000'001
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1}, .amount = 499'999'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1}, .amount = 500'000'000, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1}, .amount = 500'000'001, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1}, .amount = 500'000'002, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1}, .amount = 500'000'003, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2}, .amount = 499'999'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2}, .amount = 500'000'000, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 3}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 3}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 3}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 3}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 3}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 4}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 4}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 4}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 4}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 4}, .amount = 500'000'003, .expected = tesSUCCESS},
        // total 1'000'000'001, sharesTotal 2'000'000'000, amount 500'000'001
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'998}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'998}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'998}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'998}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'998}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'999}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'999}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'999}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'999}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'999'999'999}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'000}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'000}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'000}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'000}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'000}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'001}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'001}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'001}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'001}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'001}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'002}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'002}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'002}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'002}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 2'000'000'002}, .amount = 500'000'003, .expected = tesSUCCESS},
        // total 1'000'000'001, sharesTotal 1'000'000'000, amount 500'000'001
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'998}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'998}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'998}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'998}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'998}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'999}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'999}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'999}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'999}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 999'999'999}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'000}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'000}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'000}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'000}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'000}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .amount = 500'000'003, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'002}, .amount = 499'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'002}, .amount = 500'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'002}, .amount = 500'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'002}, .amount = 500'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'002}, .amount = 500'000'003, .expected = tesSUCCESS},
    };
    // FV_M2_3 (C++ behaviour pinned as expected): the charge rounds to nearest.
    static constexpr DepositCase kChargeRoundingVerdict[] = {
        // charge 2.5 rounds to 2 and fits; half-up would charge 3, past the maximum
        {.vault = {.available = 5, .maximum = 7, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        // charge 1.5 rounds to 2, past the maximum; flooring would charge 1 and fit
        {.vault = {.available = 3, .maximum = 4, .sharesTotal = 2}, .amount = 2, .expected = tecLIMIT_EXCEEDED},
    };
    static constexpr DepositCase kClampToZero[] = {
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS},
        // total 2, sharesTotal 2'000, amount 1
        {.vault = {.available = 2, .sharesTotal = 1'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 1'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 2'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'002}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2'002}, .amount = 3, .expected = tesSUCCESS},
        // total 2, sharesTotal 9'999'999'999'999'996, amount 1
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'002}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 9'999'999'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'998'999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'000}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'000}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'000}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'001}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'001}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'002}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'000'000'002}, .amount = 3, .expected = tesSUCCESS},
    };
    static constexpr DepositCase kShareMintCap[] = {
        // total 8'000'000'000'000'000, sharesTotal 9'223'372'036'854'774'655, amount 1
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'653}, .amount = 2, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'653}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'654}, .amount = 2, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'654}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'655}, .amount = 2, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'655}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'656}, .amount = 2, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'656}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'657}, .amount = 2, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'657}, .amount = 3, .expected = tecPATH_DRY},
    };
    static constexpr DepositCase kShareMintCapIntegral[] = {
        // total 8'000'000'000'000'000, sharesTotal 9'223'372'036'854'774'655, amount 1
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'653}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'654}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'655}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'656}, .amount = 1, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'657}, .amount = 1, .expected = tecPATH_DRY},
    };
    static constexpr DepositCase kShareMintCapIou[] = {
        // total 8'000'000'000'000'000, sharesTotal 9'223'372'036'854'774'655, amount 1
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'653}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'654}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'655}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'656}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'774'657}, .amount = 1, .expected = tecPRECISION_LOSS},
        // total 8'000'000'000'000'000, sharesTotal 9'223'372'036'854'773'502, amount 2: a one-unit charge mints up to exactly the cap
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'500}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'500}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'500}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'500}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'501}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'501}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'501}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'501}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'502}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'502}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'502}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'502}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'503}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'503}, .amount = 2, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'503}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'503}, .amount = 4, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'504}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'504}, .amount = 2, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'504}, .amount = 3, .expected = tecPATH_DRY},
        {.vault = {.available = 8'000'000'000'000'000, .sharesTotal = 9'223'372'036'854'773'504}, .amount = 4, .expected = tecPATH_DRY},
    };
    static constexpr DepositCase kSubGridAmount[] = {
        // mantissa 1'000'000'000'000'000
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 999'999'999'999'998, .expected = tecPRECISION_LOSS, .exponent = -15},
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 999'999'999'999'999, .expected = tecPRECISION_LOSS, .exponent = -15},
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 1'000'000'000'000'000, .expected = tesSUCCESS, .exponent = -15},
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 1'000'000'000'000'001, .expected = tesSUCCESS, .exponent = -15},
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 1'000'000'000'000'002, .expected = tesSUCCESS, .exponent = -15},
    };
    static constexpr DepositCase kShareOverflow[] = {
        // mantissa 9'223'372'036'854'775
        {.vault = {}, .amount = 9'223'372'036'854'773, .expected = tecLIMIT_EXCEEDED, .exponent = 3},
        {.vault = {}, .amount = 9'223'372'036'854'774, .expected = tecLIMIT_EXCEEDED, .exponent = 3},
        {.vault = {}, .amount = 9'223'372'036'854'775, .expected = tecLIMIT_EXCEEDED, .exponent = 3},
        {.vault = {}, .amount = 9'223'372'036'854'776, .expected = tecPATH_DRY, .exponent = 3},
        {.vault = {}, .amount = 9'223'372'036'854'777, .expected = tecPATH_DRY, .exponent = 3},
    };
    static constexpr DepositCase kDonation[] = {
        // yield 0, total 8'999'999'999'999'999, amount 1
        {.vault = {.available = 8'999'999'999'999'998, .sharesTotal = 8'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS, .donate = true},
        {.vault = {.available = 8'999'999'999'999'998, .sharesTotal = 8'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS, .donate = true},
        {.vault = {.available = 8'999'999'999'999'998, .sharesTotal = 8'999'999'999'999'998}, .amount = 3, .expected = tecLIMIT_EXCEEDED, .donate = true},
        {.vault = {.available = 8'999'999'999'999'999, .sharesTotal = 8'999'999'999'999'999}, .amount = 1, .expected = tesSUCCESS, .donate = true},
        {.vault = {.available = 8'999'999'999'999'999, .sharesTotal = 8'999'999'999'999'999}, .amount = 2, .expected = tecLIMIT_EXCEEDED, .donate = true},
        // maximum 1'000'000'000, total 999'999'999, amount 1
        {.vault = {.available = 999'999'998, .maximum = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 1, .expected = tesSUCCESS, .donate = true},
        {.vault = {.available = 999'999'998, .maximum = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 2, .expected = tesSUCCESS, .donate = true},
        {.vault = {.available = 999'999'998, .maximum = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 3, .expected = tecLIMIT_EXCEEDED, .donate = true},
        {.vault = {.available = 999'999'999, .maximum = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 1, .expected = tesSUCCESS, .donate = true},
        {.vault = {.available = 999'999'999, .maximum = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 2, .expected = tecLIMIT_EXCEEDED, .donate = true},
        // deposits blocked, empty, insolvent
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000, .depositBlocked = true}, .amount = 1, .expected = tecLOCKED, .donate = true},
        {.vault = {}, .amount = 1, .expected = tecNO_PERMISSION, .donate = true},
        {.vault = {.sharesTotal = 1'000'000'000}, .amount = 1, .expected = tesSUCCESS, .donate = true},
        {.vault = {.sharesTotal = 1'000'000'000}, .amount = 1'000, .expected = tesSUCCESS, .donate = true},
    };
    static constexpr DepositCase kDonationSubGrid[] = {
        // mantissa 1'000'000'000'000'000
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 999'999'999'999'998, .expected = tecPRECISION_LOSS, .exponent = -15, .donate = true},
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 999'999'999'999'999, .expected = tecPRECISION_LOSS, .exponent = -15, .donate = true},
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 1'000'000'000'000'000, .expected = tesSUCCESS, .exponent = -15, .donate = true},
        {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000}, .amount = 1'000'000'000'000'001, .expected = tesSUCCESS, .exponent = -15, .donate = true},
    };
    static constexpr DepositCase kLossIgnored[] = {
        // total 2 (loss 1), sharesTotal 1, amount 2
        {.vault = {.available = 1, .deployed = 1, .loss = 1, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1, .deployed = 1, .loss = 1, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .loss = 1, .sharesTotal = 1}, .amount = 3, .expected = tesSUCCESS},
        // total 1'000'000'000 (loss 500'000'000), sharesTotal 1, amount 1'000'000'000
        {.vault = {.available = 400'000'000, .deployed = 600'000'000, .loss = 500'000'000, .sharesTotal = 1}, .amount = 500'000'000, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 400'000'000, .deployed = 600'000'000, .loss = 500'000'000, .sharesTotal = 1}, .amount = 999'999'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 400'000'000, .deployed = 600'000'000, .loss = 500'000'000, .sharesTotal = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 400'000'000, .deployed = 600'000'000, .loss = 500'000'000, .sharesTotal = 1}, .amount = 1'000'000'001, .expected = tesSUCCESS},
    };
    static constexpr DepositCase kFirstDeposit[] = {
        {.vault = {}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {}, .amount = 1'000'000'000, .expected = tesSUCCESS},
    };
    static constexpr DepositCase kDepositLocked[] = {
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000, .depositBlocked = true}, .amount = 1, .expected = tecLOCKED},
        {.vault = {.sharesTotal = 1'000'000'000}, .amount = 1, .expected = tecLOCKED},
    };
    // clang-format on

    // Runs every list on the vaults staged open-ended or, when `closed`, closed-ended in
    // Subscription.
    void
    runDepositBoundaries(jtx::Env& env, Setup const& s, bool closed)
    {
        std::uint32_t const p = parentCloseTime(env);
        auto const run = [&](std::string const& name,
                             TestVaults const& vaults,
                             std::span<DepositCase const> cases) {
            for (auto const& [vault, depositor] : vaults)
            {
                beginCase(("deposit " + vaultName(env, vault) + " " + name +
                           (closed ? ", closed-ended" : ""))
                              .c_str());
                for (auto const& [row, amount, expected, exponent, donate] : cases)
                {
                    StagedVault staged = row;
                    if (closed)
                    {
                        staged.subscriptionDate = p + 1'000;
                        staged.redemptionDate = p + 1'001'000;
                    }
                    STAmount const deposit = vaultUnits(env, vault, amount, exponent);
                    // Only the owner may donate. An IOU owner or non-issuer depositor holds exactly
                    // the amount.
                    jtx::Account const& from = donate ? s.owner : depositor;
                    StagedAmounts const amounts =
                        fundDepositor(stagedAmounts(env, vault, staged), from, deposit);
                    AppliedVaultTx const cpp =
                        applyDeposit(env, vault, from, amounts, deposit, donate);
                    LeanVaultResult const lean = leanVaultDeposit(cpp.pre, deposit, donate, p);
                    expectSame(*this, sampleText(staged, deposit), cpp, lean, expected);
                }
            }
        };
        // An IOU list again with the funded non-issuer holder, which C++ moves over a trust line.
        auto const runIou = [&](std::string const& name,
                                TestVaults const& vaults,
                                std::span<DepositCase const> cases) {
            run(name, vaults, cases);
            run(name + ", non-issuer", s.iouHolder, cases);
        };

        runIou("open limit", s.all, kOpenLimit);
        runIou("assets maximum", s.all, kAssetsMaximum);
        // An IOU charge below one unit floors to zero where XRP and MPT round it up to one, so the
        // rows that hit it are split by vault set.
        runIou("zero shares", s.all, kZeroShares);
        run("zero shares, charge rounds up", s.integral, kZeroSharesIntegral);
        runIou("zero shares, charge floors", s.ious, kZeroSharesIou);
        run("charge rounding", s.integral, kChargeRounding);
        run("charge rounding verdict", s.integral, kChargeRoundingVerdict);
        runIou("sub-grid amount", s.ious, kSubGridAmount);
        runIou("share overflow", s.ious, kShareOverflow);
        runIou("clamp to zero", s.ious, kClampToZero);
        runIou("share mint cap", s.all, kShareMintCap);
        run("share mint cap, charge rounds up", s.integral, kShareMintCapIntegral);
        runIou("share mint cap, charge floors", s.ious, kShareMintCapIou);
        run("donation", s.all, kDonation);
        run("donation, sub-grid amount", s.ious, kDonationSubGrid);
        runIou("loss ignored", s.all, kLossIgnored);
        runIou("first deposit", s.all, kFirstDeposit);
        runIou("deposit locked", s.all, kDepositLocked);
    }

    void
    testDepositBoundaries(jtx::Env& env, Setup const& s)
    {
        runDepositBoundaries(env, s, false);
    }

    // The same lists in Subscription, and the subscription date: a plain deposit of one unit is
    // accepted while P <= subscription date and tecEXPIRED after it. Those rows put the
    // subscription date at P + subscription and the redemption date at P + redemption.
    void
    testClosedEndedDepositBoundaries(jtx::Env& env, Setup const& s)
    {
        runDepositBoundaries(env, s, true);

        struct DateCase
        {
            StagedVault vault;
            std::int64_t subscription;
            std::int64_t redemption;
            std::int64_t amount;
            TER expected;
        };
        // clang-format off
        static constexpr DateCase kSubscriptionDate[] = {
            // gap 180, offset 0
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = -2, .redemption = 178, .amount = 1, .expected = tecEXPIRED},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = -1, .redemption = 179, .amount = 1, .expected = tecEXPIRED},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 0, .redemption = 180, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 1, .redemption = 181, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 2, .redemption = 182, .amount = 1, .expected = tesSUCCESS},
            // gap 1'000'000, offset 0
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = -2, .redemption = 999'998, .amount = 1, .expected = tecEXPIRED},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = -1, .redemption = 999'999, .amount = 1, .expected = tecEXPIRED},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 0, .redemption = 1'000'000, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 1, .redemption = 1'000'001, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 2, .redemption = 1'000'002, .amount = 1, .expected = tesSUCCESS},
            // gap 946'708'559, offset 0
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = -2, .redemption = 946'708'557, .amount = 1, .expected = tecEXPIRED},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = -1, .redemption = 946'708'558, .amount = 1, .expected = tecEXPIRED},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 0, .redemption = 946'708'559, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 1, .redemption = 946'708'560, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .subscription = 2, .redemption = 946'708'561, .amount = 1, .expected = tesSUCCESS},
        };
        // clang-format on

        for (auto const& [vault, depositor] : s.all)
        {
            beginCase(("deposit " + vaultName(env, vault) + " subscription date").c_str());
            std::uint32_t const p = parentCloseTime(env);
            for (auto const& [row, subscription, redemption, amount, expected] : kSubscriptionDate)
            {
                StagedVault staged = row;
                staged.subscriptionDate = static_cast<std::uint32_t>(p + subscription);
                staged.redemptionDate = static_cast<std::uint32_t>(p + redemption);
                STAmount const deposit = vaultUnits(env, vault, amount);
                AppliedVaultTx const cpp = applyDeposit(env, vault, depositor, staged, deposit);
                LeanVaultResult const lean = leanVaultDeposit(cpp.pre, deposit, false, p);
                expectSame(*this, sampleText(staged, deposit), cpp, lean, expected);
            }
        }
    }

    // Phase matrix: a plain deposit of 100 into a 1000 IOU vault is rejected once the vault is past
    // Subscription, a donation (by the owner, who holds no shares) never is. Covered at the
    // subscription date by testClosedEndedDepositBoundaries.
    void
    testClosedEndedDeposit(
        jtx::Env& env,
        Setup const& s,
        VaultPhase phase,
        bool isDonation,
        TER expected,
        bool onDate = false)
    {
        testcase((isDonation ? "donate " : "deposit ") + phaseName(phase, onDate));
        Keylet const& vault = s.iouDefaultScaleVault;
        jtx::Account const& depositor = isDonation ? s.owner : s.holder;
        STAmount const amount = s.issuer["USD"](100);
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), phase, std::nullopt, onDate);
        if (isDonation)
            staged.holderShares.reset();
        expectStagedDeposit(
            env,
            vault,
            depositor,
            fundDepositor(staged, depositor, amount),
            amount,
            expected,
            isDonation);
    }

    void
    runTests() override
    {
        using namespace jtx;

        Env env{*this, vaultTestAmendments()};
        Setup const s = setup(env);

        testVaultDepositXRP(
            env, s.xrpVault, s.depositor, XRP(0), drops(1), tesSUCCESS);  // minimum deposit
        testVaultDepositXRP(env, s.xrpVault, s.depositor, XRP(0), XRP(1'000), tesSUCCESS);
        // Open limit: 9e15 drops. Covered by testDepositBoundaries.
        testVaultDepositXRP(
            env, s.xrpVault, s.depositor, XRP(0), drops(kOpenLimitUnits), tesSUCCESS);
        testVaultDepositXRP(
            env, s.xrpVault, s.depositor, XRP(0), drops(kOpenLimitUnits + 1), tecLIMIT_EXCEEDED);
        testVaultDepositXRP(
            env, s.xrpVault, s.depositor, XRP(1'000), XRP(1'000), tesSUCCESS);  // non-empty vault
        testVaultDepositXRP(
            env,
            s.xrpVault,
            s.depositor,
            XRP(1'000),
            drops(1),
            tesSUCCESS);  // minimum deposit, non-empty

        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.holder, Number{0}, Number{1}, tesSUCCESS);
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.holder, Number{0}, Number{1'000}, tesSUCCESS);
        // Open limit at scale 6: 9e9. It keeps the shares (amount * 1e6) far below INT64_MAX.
        // Covered by testDepositBoundaries.
        Number const iouOpenLimit{kOpenLimitUnits, -6};
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.holder, Number{0}, iouOpenLimit, tesSUCCESS);
        testVaultDepositIOU(
            env,
            s.iouDefaultScaleVault,
            s.holder,
            Number{0},
            iouOpenLimit + Number{1, -6},
            tecLIMIT_EXCEEDED);
        // 1e10 at scale 6 needs 17 digits: the total would leave the base exponent.
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.holder, Number{0}, Number{1, 10}, tecLIMIT_EXCEEDED);
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.issuer, Number{0}, Number{1}, tesSUCCESS);
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.issuer, Number{0}, iouOpenLimit, tesSUCCESS);
        testVaultDepositIOU(
            env,
            s.iouDefaultScaleVault,
            s.issuer,
            Number{0},
            iouOpenLimit + Number{1, -6},
            tecLIMIT_EXCEEDED);

        // covered by testDepositBoundaries
        testVaultDepositIOU(
            env,
            s.iouDefaultScaleVault,
            s.issuer,
            Number{0},
            Number{9'999'999'999'999'999LL, 80},
            tecPATH_DRY);
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.issuer, Number{0}, Number{1, -80}, tecPRECISION_LOSS);

        testRoundedDepositSuccess(env, s.iouDefaultScaleVault, s.issuer);
        testRoundedDepositBelowVaultScale(env, s.iouDefaultScaleVault, s.holder);
        testRoundedDepositBelowVaultScale(env, s.iouDefaultScaleVault, s.issuer);
        // sanity: a normal deposit into the same non-empty vault still succeeds
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.holder, Number{1, 9}, Number{1'000}, tesSUCCESS);

        testVaultDepositMPT(env, s.mptVault, s.depositor, 0, 1, tesSUCCESS);
        testVaultDepositMPT(env, s.mptVault, s.depositor, 0, 1'000, tesSUCCESS);
        // Open limit: 9e15 units, far below the share type maximum INT64_MAX. Covered by
        // testDepositBoundaries.
        testVaultDepositMPT(env, s.mptVault, s.depositor, 0, kOpenLimitUnits, tesSUCCESS);
        testVaultDepositMPT(
            env, s.mptVault, s.depositor, 1'000, 1'000, tesSUCCESS);  // non-empty vault
        testVaultDepositMPT(env, s.mptVault, s.depositor, 1, kOpenLimitUnits - 1, tesSUCCESS);
        testVaultDepositMPT(env, s.mptVault, s.depositor, kOpenLimitUnits - 1, 1, tesSUCCESS);
        testVaultDepositMPT(
            env, s.mptVault, s.depositor, kOpenLimitUnits - 1, 2, tecLIMIT_EXCEEDED);

        // Truncated to the 1e-6 grid on both sides. Covered by testDepositBoundaries.
        testVaultDepositIOU(
            env,
            s.iouDefaultScaleVault,
            s.holder,
            Number{1, 9},
            Number{100'000'006, -7},
            tesSUCCESS);
        testVaultDepositIOU(
            env,
            s.iouDefaultScaleVault,
            s.holder,
            Number{1, 9},
            Number{100'000'001, -7},
            tesSUCCESS);

        // Empty-vault share truncation (C++ truncates toward zero, not to-nearest):
        // 1.5e-6 USD * 1e6 scale = 1.5 shares -> 1.
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.issuer, Number{0}, Number{15, -7}, tesSUCCESS);
        // Zero-share deposit is rejected: 0.6e-6 USD * 1e6 = 0.6 shares -> 0 -> tecPRECISION_LOSS.
        // covered by testDepositBoundaries (preclaim rounds it to zero first)
        testVaultDepositIOU(
            env, s.iouDefaultScaleVault, s.issuer, Number{0}, Number{6, -7}, tecPRECISION_LOSS);

        testVaultDepositExchangeRate(env, s.iouDefaultScaleVault, s.issuer);

        // Extreme NAV ratio AssetsTotal >> SharesTotal: a unit deposit buys zero shares.
        // covered by the zero shares cases of testDepositBoundaries
        testVaultDepositUpdatedStateMPT(
            env, s.mptVault, s.depositor, Number{1, 18}, 1, 1, tecPRECISION_LOSS);
        // Share price 3e-7: one grid unit buys 3 shares worth 9e-7, which clamps to nothing.
        // covered by the clamp to zero cases of testDepositBoundaries
        testVaultDepositUpdatedStateIOU(
            env,
            s.iouDefaultScaleVault,
            s.issuer,
            Number{1'000},
            3'333'333'333ULL,
            Number{1, -6},
            tecPRECISION_LOSS);
        // AssetsTotal near the STAmount exponent ceiling: a small IOU deposit rounds to zero.
        testRoundedDepositUpdatedStateIOU(
            env,
            s.iouDefaultScaleVault,
            s.issuer,
            Number{9'999'999'999'999'999LL, 80},
            Number{1},
            tecPRECISION_LOSS);
        testRoundedDepositOverflow(env, s.iouDefaultScaleVault, s.issuer);

        // Insolvent vault (assetsTotal=0, sharesTotal>0): deposits are blocked with tecLOCKED.
        testVaultDepositUpdatedStateMPT(
            env, s.mptVault, s.depositor, Number{0}, 1'000'000, 1'000, tecLOCKED);
        testVaultDepositBlocked(env, s.xrpVault, s.depositor);
        // Unrealized yield counts toward the open-limit capacity: 10 under the limit (one share
        // per unit) with 10 of yield rejects one unit, with 9 of yield it fits exactly.
        // covered by testDepositBoundaries
        testVaultDepositUpdatedStateMPT(
            env,
            s.mptVault,
            s.depositor,
            Number{kOpenLimitUnits - 10},
            static_cast<std::uint64_t>(kOpenLimitUnits - 10),
            1,
            tecLIMIT_EXCEEDED,
            Number{10});
        testVaultDepositUpdatedStateMPT(
            env,
            s.mptVault,
            s.depositor,
            Number{kOpenLimitUnits - 10},
            static_cast<std::uint64_t>(kOpenLimitUnits - 10),
            1,
            tesSUCCESS,
            Number{9});
        testVaultDonationEmptyVault(env, s.xrpVault, s.owner);
        testVaultDepositCap(env, s.mptVault, s.depositor, Number{1'000}, tecLIMIT_EXCEEDED);
        testVaultDepositCap(env, s.mptVault, s.depositor, Number{2'000}, tesSUCCESS);

        // Open discrepancies, disabled until the C++ code is fixed.
        // clang-format off
        // testDepositDilution();          // FV_M2_8_c: deposit lowers the share price (both)
        // testDepositPastOpenLimit(env, s.iouDefaultScaleVault, s.issuer, Number{9'999'999'999'999'999LL, -6}, Number{1, -5});  // FV_M2_15_b

        // Properties both sides now satisfy, kept as regression tests.
        testVaultDepositOvervaluedShares(env, s.xrpVault, s.depositor);
        testDepositAppliedDelta();
        testVaultDonationInsolvent(env, s.mptVault, s.owner);
        // FV_M2_15: 899999.9999999999 is at the scale-10 open limit (9e5); +5 passes it.
        // covered by testDepositBoundaries
        testDepositPastOpenLimit(env, s.iouMaxScaleVault, s.issuer, Number{8'999'999'999'999'999LL, -10}, Number{5});
        // clang-format on

        testDepositBoundaries(env, s);

        testClosedEndedDeposit(env, s, VaultPhase::NoPhase, false, tesSUCCESS);
        testClosedEndedDeposit(env, s, VaultPhase::Subscription, false, tesSUCCESS);
        testClosedEndedDeposit(env, s, VaultPhase::Subscription, false, tesSUCCESS, kOnDate);
        testClosedEndedDeposit(env, s, VaultPhase::Investment, false, tecEXPIRED);
        testClosedEndedDeposit(env, s, VaultPhase::Redemption, false, tecEXPIRED, kOnDate);
        testClosedEndedDeposit(env, s, VaultPhase::Redemption, false, tecEXPIRED);
        // Donations are not subject to the phase check.
        testClosedEndedDeposit(env, s, VaultPhase::NoPhase, true, tesSUCCESS);
        testClosedEndedDeposit(env, s, VaultPhase::Subscription, true, tesSUCCESS);
        testClosedEndedDeposit(env, s, VaultPhase::Investment, true, tesSUCCESS);
        testClosedEndedDeposit(env, s, VaultPhase::Redemption, true, tesSUCCESS);

        testClosedEndedDepositBoundaries(env, s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
