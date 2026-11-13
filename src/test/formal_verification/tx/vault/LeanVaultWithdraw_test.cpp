#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
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

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

struct WithdrawCase
{
    StagedVault vault;
    std::int64_t amount;
    TER expected;
    // The amount is in shares, not vault assets.
    bool byShares{};
    // Set: the available assets are vault.available * 10^availableExponent of the asset rather
    // than vault units, to reach past the vault grid.
    std::optional<int> availableExponent{};
    // The model error a tefEXCEPTION row expects.
    std::optional<LeanError> leanError{};
};

class LeanVaultWithdraw_test : public LeanSuite
{
    // Staged withdrawals run on a throwaway view of one shared ledger and expect their verdict on
    // both sides.
    // Staged states may be unreachable by any transaction: a verdict compares model and C++ on the
    // same pre-state and does not claim the state is reachable (see stageVault).

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
        Vault const state = readVaultState(env, vaultKeylet, asset);
        bool const byShares = amount.asset() != asset;
        bool const waiveUnrealizedLoss = holderOwnsAllShares(env, vaultKeylet, withdrawer);
        LeanVaultResult const lean = leanVaultWithdraw(
            state,
            amount,
            byShares,
            parentCloseTime(env),
            waiveUnrealizedLoss,
            Number{fetchHolderShares(env, vaultKeylet, withdrawer)});
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean withdraw error");

        env(jtx::Vault::withdraw(
                {.depositor = withdrawer, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        Vault const post = readVaultState(env, vaultKeylet, asset);
        Number const storedTotal = env.le(vaultKeylet)->at(sfAssetsTotal);
        env.close();

        AppliedVaultTx const cpp{
            .pre = state,
            .ter = cppTer,
            .post = post,
            .assets = state.assetsAvailable - post.assetsAvailable,
            .shares = state.sharesTotal - post.sharesTotal,
            .asset = asset,
            .storedTotal = storedTotal,
        };
        expectSame(*this, "", cpp, lean, expected);
    }

    // Both sides withdraw `amount` from the staged vault and return `expected`, with every vault
    // field and the payout equal when both succeed; the payout is `expectedPayout` when given.
    AppliedVaultTx
    expectStagedWithdraw(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        StagedAmounts const& staged,
        STAmount const& amount,
        TER expected,
        std::optional<Number> const& expectedPayout = std::nullopt)
    {
        bool const byShares = amount.asset() != Asset{env.le(vault)->at(sfAsset)};
        AppliedVaultTx const cpp = applyWithdraw(env, vault, holder, staged, amount);
        LeanVaultResult const lean =
            leanWithdraw(cpp, staged, amount, byShares, parentCloseTime(env));
        std::string const at = sampleText(staged, amount);
        expectLawful(lean);
        expectSame(*this, at, cpp, lean, expected);
        if (expectedPayout && cpp.ter == tesSUCCESS)
        {
            BEAST_EXPECTS(
                cpp.assets && *cpp.assets == *expectedPayout,
                at + "payout " + (cpp.assets ? to_string(*cpp.assets) : std::string{"none"}) +
                    " expected " + to_string(*expectedPayout));
        }
        return cpp;
    }

    // A vault after a first deposit of `seed` by the holder, who owns the seed * 10^scale shares.
    static StagedAmounts
    seededVault(jtx::Env& env, Keylet const& vault, STAmount const& seed)
    {
        int const scale = env.le(vault)->at(sfScale);
        auto const shares =
            static_cast<std::uint64_t>(static_cast<std::int64_t>(Number{seed} * Number{1, scale}));
        return StagedAmounts{.available = seed, .sharesTotal = shares, .holderShares = shares};
    }

    // A state staged over a vault the holder seeded with 1000 units (the holder keeps the seed's
    // shares); the total splits into `available` and the deployed rest.
    static StagedAmounts
    overSeed(
        jtx::Env& env,
        Keylet const& vault,
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal)
    {
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, Number{1'000}});
        staged.available = STAmount{asset, assetsAvailable};
        staged.deployed = STAmount{asset, assetsTotal - assetsAvailable};
        staged.sharesTotal = sharesTotal;
        return staged;
    }

    void
    testWithdrawXRP(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        STAmount seed,
        STAmount amount,
        TER expected)
    {
        testcase("withdraw XRP " + amount.getText() + " from " + seed.getText());
        expectStagedWithdraw(env, vault, holder, seededVault(env, vault, seed), amount, expected);
    }

    void
    testWithdrawIOU(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number seed,
        Number amount,
        TER expected)
    {
        testcase("withdraw IOU " + to_string(amount) + " from " + to_string(seed));
        Asset const asset = env.le(vault)->at(sfAsset);
        expectStagedWithdraw(
            env,
            vault,
            holder,
            seededVault(env, vault, STAmount{asset, seed}),
            STAmount{asset, amount},
            expected);
    }

    void
    testWithdrawMPT(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        std::int64_t seed,
        std::int64_t amount,
        TER expected)
    {
        testcase("withdraw MPT " + std::to_string(amount) + " from " + std::to_string(seed));
        expectStagedWithdraw(
            env,
            vault,
            holder,
            seededVault(env, vault, vaultUnits(env, vault, seed)),
            vaultUnits(env, vault, amount),
            expected);
    }

    void
    testWithdrawAllShares(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("withdraw all shares (full redemption)");
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged = seededVault(env, vault, STAmount{asset, Number{1'000}});
        STAmount const allShares{shareIssue(env, vault), staged.sharesTotal};
        expectStagedWithdraw(env, vault, holder, staged, allShares, tesSUCCESS);
    }

    // Validate sharesToAssetsWithdraw through the withdraw tx
    void
    testSharesToAssets(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number seed,
        Number donation,
        std::int64_t shareCount)
    {
        testcase(
            "sharesToAssetsWithdraw " + std::to_string(shareCount) +
            " shares (seed=" + to_string(seed) + ", donation=" + to_string(donation) + ")");

        // A donation adds assets but no shares.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, seed});
        staged.available = STAmount{asset, seed + donation};
        STAmount const shares{shareIssue(env, vault), shareCount};
        AppliedVaultTx const cpp =
            expectStagedWithdraw(env, vault, holder, staged, shares, tesSUCCESS);
        Number const paid = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;

        LeanSharesToAssetsResult const lean = leanSharesToAssetsWithdraw(cpp.pre, shares, false);
        expectLawful(lean);
        BEAST_EXPECTS(!lean.leanError.has_value(), "lean sharesToAssetsWithdraw error");
        // The payout is the conversion clamped toward zero to the vault grid.
        Number const conversion{lean.assets};
        BEAST_EXPECTS(
            (conversion >= paid && conversion - paid < Number{1, -static_cast<int>(cpp.pre.scale)}),
            "conversion " + to_string(conversion) + " is not the payout " + to_string(paid) +
                " before the clamp");
    }

    // Force an extreme vault state a real deposit cannot reach, then withdraw and compare.
    void
    testWithdrawUpdatedState(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal,
        std::int64_t shareAmount,
        TER expected)
    {
        testcase(
            "withdraw updated-state shares=" + std::to_string(shareAmount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", assetsAvailable=" + to_string(assetsAvailable) +
            ", sharesTotal=" + std::to_string(sharesTotal) + ")");
        expectStagedWithdraw(
            env,
            vault,
            holder,
            overSeed(env, vault, assetsTotal, assetsAvailable, sharesTotal),
            STAmount{shareIssue(env, vault), shareAmount},
            expected);
    }

    // Stage an IOU vault past the open limit (a deposit cannot reach it), then withdraw by assets.
    void
    testWithdrawAssetsStaged(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        std::uint64_t sharesTotal,
        Number const& amount,
        TER expected)
    {
        testcase("STAGED withdraw IOU " + to_string(amount) + " from " + to_string(assetsTotal));
        Asset const asset = env.le(vault)->at(sfAsset);
        expectStagedWithdraw(
            env,
            vault,
            holder,
            overSeed(env, vault, assetsTotal, assetsTotal, sharesTotal),
            STAmount{asset, amount},
            expected);
    }

    // Two holders: the holder redeems one share more than they own. The vault could pay it, the
    // holder's balance cannot.
    // A vault nobody deposited into: no shares outstanding, so nobody is the sole holder.
    void
    testWithdrawFromEmptyVault(bool byShares, TER expected)
    {
        using namespace jtx;
        testcase(
            std::string("withdraw from an empty vault by ") + (byShares ? "shares" : "assets"));

        Env env{*this, vaultTestAmendments()};
        Account const owner{"owner"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, holder);
        env.close();

        auto const vaultKeylet = createVault(env, owner, xrpIssue());
        STAmount const amount =
            byShares ? STAmount{shareIssue(env, vaultKeylet), 1} : STAmount{drops(100)};
        compareWithdraw(env, vaultKeylet, holder, xrpIssue(), amount, expected);
    }

    void
    testWithdrawMoreSharesThanHeld(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("withdraw more shares than the holder owns");
        // Two holders deposited 1000 each; the holder owns half the shares.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, Number{2'000}});
        staged.holderShares = staged.sharesTotal / 2;
        STAmount const tooMany{shareIssue(env, vault), *staged.holderShares + 1};
        expectStagedWithdraw(env, vault, holder, staged, tooMany, tecINSUFFICIENT_FUNDS);
    }

    // Stage an MPT vault with a share price below one unit and withdraw a few shares.
    void
    testWithdrawUpdatedStateMPT(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        std::uint64_t sharesTotal,
        std::int64_t shareAmount,
        TER expected)
    {
        testcase(
            "withdraw updated-state MPT shares=" + std::to_string(shareAmount) + " (assetsTotal=" +
            to_string(assetsTotal) + ", sharesTotal=" + std::to_string(sharesTotal) + ")");
        expectStagedWithdraw(
            env,
            vault,
            holder,
            overSeed(env, vault, assetsTotal, assetsTotal, sharesTotal),
            STAmount{shareIssue(env, vault), shareAmount},
            expected);
    }

    // A fully impaired vault (the whole deployed total is an unrealized loss) with two holders:
    // without the sole-holder waiver the net asset value is zero, and a withdrawal by shares
    // burns the shares for nothing on both sides.
    // Known C++ defect pinned as expected (no finding id): the burn for a zero payout.
    void
    testWithdrawFromFullyImpairedVault(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder)
    {
        testcase("withdraw shares from a fully impaired vault with two holders");
        // The holder deposited 1000 and another holder 10, then the whole total was lost.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = overSeed(env, vault, Number{1'010}, Number{0}, 0);
        staged.sharesTotal = seededVault(env, vault, STAmount{asset, Number{1'010}}).sharesTotal;
        staged.loss = STAmount{asset, Number{1'010}};
        expectStagedWithdraw(
            env, vault, holder, staged, STAmount{shareIssue(env, vault), 100'000'000}, tesSUCCESS);
        // By assets, the zero net asset value converts to zero shares: rejected.
        expectStagedWithdraw(
            env, vault, holder, staged, STAmount{asset, Number{1}}, tecPRECISION_LOSS);
    }

    // Withdraw by assets from a vault whose sharesTotal is INT64_MAX, so the share computation
    // (sharesTotal * assets / NAV) overflows the MPT domain.
    void
    testWithdrawAssetsShareOverflow(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        TER expected)
    {
        testcase("withdraw assets with INT64_MAX shares");
        Asset const asset = env.le(vault)->at(sfAsset);
        expectStagedWithdraw(
            env,
            vault,
            holder,
            overSeed(env, vault, Number{1}, Number{1}, kMaxMpTokenAmount),
            STAmount{asset, Number{1'000}},
            expected);
    }

    // FV_M2_3 (C++ behaviour pinned as expected): a share withdrawal pays round-to-nearest, so a
    // single-share withdraw can pay more than the share is worth; the model rounds the same way.
    void
    testWithdrawOvervaluedShares(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("withdraw overvalued shares");
        // 3 shares back 5 drops (1 share = 1.667 drops): a single-share withdraw pays
        // round(1.667) = 2 on both sides.
        StagedAmounts staged = seededVault(env, vault, vaultUnits(env, vault, 3));
        staged.available = vaultUnits(env, vault, 5);
        expectStagedWithdraw(
            env, vault, holder, staged, STAmount{shareIssue(env, vault), 1}, tesSUCCESS);
    }

    // FV_M2_4 (regression): a withdrawal too small to debit assetsTotal (the debit rounds back to
    // the old value) used to pay the withdrawer and trip the global invariant; both sides now
    // reject it with tecPRECISION_LOSS. A ~1e10 total is past the open limit (9e9 at scale 6),
    // so it is staged.
    void
    testWithdrawPrecisionLossStaged(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal)
    {
        testcase("STAGED withdraw 1e-6 from total " + to_string(assetsTotal));
        Asset const asset = env.le(vault)->at(sfAsset);
        expectStagedWithdraw(
            env,
            vault,
            holder,
            overSeed(env, vault, assetsTotal, assetsTotal, 10'000'000'000'000'009ULL),
            STAmount{asset, Number{1, -6}},
            tecPRECISION_LOSS);
    }

    // Finding (FV_M2_6, regression): preclaim computes waiveUnrealizedLoss (Yes for a sole
    // shareholder) and doApply used to ignore it, paying the withdrawer less. Both now waive.
    void
    testWithdrawWaiveLoss()
    {
        using namespace jtx;
        testcase("withdraw sole shareholder waives unrealized loss");

        Env env{*this, vaultTestAmendments()};
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

        // The lender is the sole shareholder.
        jtx::Vault vault{env};
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

        // A loan impaired immediately gives the vault a real unrealized loss.
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
            // A loan can only be impaired once its payment is late.
            std::uint32_t const dueDate = env.le(loanKeylet)->at(sfNextPaymentDueDate);
            env.close(NetClock::time_point{NetClock::duration{dueDate + 1}});
            env(manage(lender, loanKeylet.key, tfLoanImpair), jtx::Ter(tesSUCCESS));
            env.close();
        }
        BEAST_EXPECT(env.le(vaultKeylet)->at(sfLossUnrealized) != Number{0});
        env.close(subscriptionDate + investmentWindow + std::chrono::seconds{1});

        STAmount const shares{shareIssue(env, vaultKeylet), 100'000'000};
        compareWithdraw(env, vaultKeylet, lender, asset.raw(), shares, tesSUCCESS);
    }

    // Finding (FV_M2_9, both sides): a sole shareholder witdrawing all outstanding shares is
    // rejected tecINSUFFICIENT_FUNDS because the interior mul/div overshoots the payout one ULP
    // above assetsAvailable.
    void
    testWithdrawOvershoot()
    {
        using namespace jtx;
        testcase("withdraw all shares overshoots assetsAvailable");

        Env env{*this, vaultTestAmendments()};
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

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        // Stage assetsTotal = assetsAvailable = INT64_MAX - 1 with 3 outstanding shares. Redeeming
        // all 3: (2^63-2)*3 rounds up at 19 digits, then /3 rounds up to 2^63-1 > assetsAvailable.
        std::int64_t const nearMax = 9'223'372'036'854'775'806LL;
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{nearMax}, Number{nearMax}, 3));
        STAmount const allShares{shareIssue(env, vaultKeylet), 3};
        compareWithdraw(env, vaultKeylet, holder, asset.raw(), allShares, tesSUCCESS);
    }

    // Finding (FV_M2_13, regression): a sole shareholder's full withdrawal while the vault carries
    // an unrealized loss used to reach the final-withdrawal branch -> tefINTERNAL. A loss is backed
    // by deployed assets, and a full exit with deployed assets is now tecHAS_OBLIGATIONS.
    void
    testWithdrawFinalWithLoss(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        Number const& loss)
    {
        testcase("full withdrawal of " + to_string(assetsTotal) + " with loss " + to_string(loss));
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, assetsTotal});
        staged.available = STAmount{asset, assetsTotal - loss};
        staged.deployed = STAmount{asset, loss};
        staged.loss = STAmount{asset, loss};
        STAmount const allShares{shareIssue(env, vault), staged.sharesTotal};
        expectStagedWithdraw(env, vault, holder, staged, allShares, tecHAS_OBLIGATIONS);
    }

    // FV_M2_16 (no longer reachable): on a scale-0 IOU vault where one share is worth less than
    // the assetsTotal ULP, withdrawing all but one share pays out the whole balance, draining
    // assetsTotal to 0 while a share stays outstanding. Such a total is now past the open limit,
    // so only a staged state reaches it; kept to show both sides agree on the staged arithmetic.
    void
    testWithdrawDrainsVault(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("partial withdrawal drains a scale-0 vault to zero");
        // Scale 0: 1 share == 1 asset unit. sharesTotal == assetsTotal == 10^17 (16-digit storage,
        // ULP 100), all held by the holder.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts const staged = seededVault(env, vault, STAmount{asset, Number{1, 17}});
        // Withdraw all but one share: both sides pay the whole balance (assetsTotal -> 0).
        STAmount const allButOne{shareIssue(env, vault), staged.sharesTotal - 1};
        expectStagedWithdraw(env, vault, holder, staged, allButOne, tesSUCCESS);
    }

    // Finding (FV_M2_8, both sides): withdraw pricing rounds in the vault's favor, but the
    // sfAssetsTotal -= update rounds again, dropping the exact difference's low digits from the
    // vault and lowering the share price. Both C++ and the model dilute.
    void
    testWithdrawDilution()
    {
        using namespace jtx;
        testcase("withdraw lowers the share price (dilution)");

        Env env{*this, vaultTestAmendments()};
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createDilutionVault(env, owner, issuer, holder, asset);

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

    // Finding (FV_M2_12, regression): a withdrawal too small to change the stored assetsTotal
    // used to burn a share (c++ -> tecINVARIANT_FAILED). Both sides now return tecPRECISION_LOSS.
    void
    testWithdrawDustDebit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Number const& assetsTotal,
        std::uint64_t sharesTotal)
    {
        testcase("withdraw one dust share (total " + to_string(assetsTotal) + ")");
        // Stage so one share is worth less than the assetsTotal precision step. Withdrawing it
        // debits an amount that rounds the stored total back unchanged. The holder seeded 1e6.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedAmounts staged = seededVault(env, vault, STAmount{asset, Number{1, 6}});
        staged.available = STAmount{asset, assetsTotal};
        staged.sharesTotal = sharesTotal;
        expectStagedWithdraw(
            env, vault, holder, staged, STAmount{shareIssue(env, vault), 1}, tecPRECISION_LOSS);
    }

    // The round-trip payout is clamped to the vault grid, so the totals move by exactly what the
    // holder receives (both C++ and the model).
    void
    testWithdrawAppliedDelta()
    {
        using namespace jtx;
        testcase("withdraw moves the vault totals by exactly the payout");

        Env env{*this, vaultTestAmendments()};
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createAppliedDeltaVault(env, owner, issuer, holder, asset);

        // Empty the holder's balance: the payout below then lands without rounding, so the
        // balance diff is the exact amount accountSend moves.
        env(pay(holder, issuer, asset(Number{993, -3})));
        env.close();

        Vault const before = readVaultState(env, vaultKeylet, asset.raw());
        BEAST_EXPECT(before.assetsTotal == Number{3});

        // Redeem a third of the holder's 7e7 shares.
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

        // C++: the vault must lose exactly what the holder received.
        Number const cppDelta = before.assetsTotal - after.assetsTotal;
        Number const received = iouBalance(env, holder, asset) - holderBefore;
        BEAST_EXPECTS(
            cppDelta == received,
            "C++ booked " + to_string(cppDelta) + " but the holder received " +
                to_string(received));

        // Model: the vault must lose exactly the payout it reports.
        Number const leanDelta = before.assetsTotal - lean.vault.assetsTotal;
        BEAST_EXPECTS(
            leanDelta == Number{lean.assets},
            "model booked " + to_string(leanDelta) + " but paid out " +
                to_string(Number{lean.assets}));

        // The paid-out amount must be on the vault scale, on both sides: the model payout
        // is the same value here.
        STAmount const receivedRounded =
            roundToVaultGrid(asset, before.scale, before.assetsAvailable, -received);
        BEAST_EXPECTS(
            Number{receivedRounded} == received,
            "the paid out " + to_string(received) + " re-rounds to " +
                to_string(Number{receivedRounded}));
    }

    // Early-exit fee rates in tenth-bips.
    static constexpr std::uint32_t kFee5Pct = 5'000;
    static constexpr std::uint32_t kFee50Pct = 50'000;
    static constexpr std::uint32_t kFee100Pct = 100'000;

    static std::string
    feeName(std::optional<std::uint32_t> earlyExitFeeRate)
    {
        if (!earlyExitFeeRate)
            return "no fee field";
        return "fee " + std::to_string(*earlyExitFeeRate) + " tenth-bips";
    }

    // The vaults a case list runs on, each with the account that withdraws from it.
    using TestVaults = std::vector<std::pair<Keylet, jtx::Account>>;

    // What every test runs on: the accounts and a vault per asset. Every staged withdrawal runs
    // on a throwaway view of this one ledger.
    struct Setup
    {
        jtx::Account owner;
        jtx::Account issuer;
        jtx::Account depositor;
        // An IOU holder that is not the issuer, with a share MPToken in the default-scale vault.
        jtx::Account holder;
        Keylet xrpVault;
        Keylet mptVault;
        Keylet iouMinScaleVault;
        Keylet iouDefaultScaleVault;
        TestVaults xrp;
        TestVaults mpt;
        TestVaults ious;
        TestVaults integral;
        TestVaults all;
        // The default-scale IOU vault with the holder as withdrawer.
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
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer, depositor, mpt(9'200'000'000'000'000)));
        env.close();

        // The IOU withdrawer is the issuer, which skips the C++-only trust-line checks.
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
        // The holder's share MPToken; its IOU balance is back to zero.
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
            .iouMinScaleVault = iouMinScaleVault,
            .iouDefaultScaleVault = iouDefaultScaleVault,
            .xrp = {{xrpVault, depositor}},
            .mpt = {{mptVault, depositor}},
            .ious = ious,
            .integral = integral,
            .all = all,
            .iouHolder = {{iouDefaultScaleVault, holder}},
        };
    }

    // Each case stages its vault (the holder owns every share unless the row sets holderShares),
    // withdraws `amount` vault units, or shares when byShares, and expects its verdict on both
    // sides. Rows are grouped by the cusp they sit around.
    // - Zero shares by assets: an amount worth trunc(shares total * amount / assets total) = 0
    //   shares is rejected (tecPRECISION_LOSS). Each cusp burns exactly one share. Where that
    //   share is worth less than one unit, XRP and MPT round its payout up to one unit and an IOU
    //   floors it to zero (tecPRECISION_LOSS), so those rows are split by vault set.
    // - Zero payout (XRP, MPT): a by-shares payout round(nav * shares / shares total) = 0 is
    //   rejected (tecPRECISION_LOSS). Each cusp pays exactly half a unit, which rounds to even (0).
    // - Clamp to zero (IOU): a by-shares payout below one grid step floors to zero
    //   (tecPRECISION_LOSS). Each cusp pays exactly one grid step.
    // - Payout range (XRP): a by-shares payout past 10^17 drops is rejected before the holder's
    //   shares are checked; each cusp pays exactly 10^17. C++ throws an uncaught runtime_error
    //   (tefEXCEPTION), the model an out-of-range error.
    // - Payout range (MPT): a by-shares payout past the MPT maximum fails (tecPATH_DRY).
    // - Payout range (IOU): a by-shares payout past the largest IOU amount fails (tecPATH_DRY).
    //   Each cusp redeems every share of a vault holding exactly that amount.
    // - To nearest (IOU): a payout of X + 1/2 units truncates below X = 10^15 and rounds to even
    //   from there. Every row succeeds; it shows in the post-state and the payout.
    // - Available: with assets deployed, a withdrawal above the available assets is rejected
    //   (tecINSUFFICIENT_FUNDS). Each cusp withdraws exactly the available assets, at price 1.
    // - Final: redeeming every share pays all available assets and is rejected while assets are
    //   deployed (tecHAS_OBLIGATIONS). Each cusp has nothing deployed, at price 1.
    // - Fully impaired: with a zero net asset value a by-shares redemption burns the shares for
    //   nothing (tesSUCCESS); one unit of net asset value makes the payout non-zero, which XRP and
    //   MPT reject as zero after rounding (tecPRECISION_LOSS) and an IOU as unavailable
    //   (tecINSUFFICIENT_FUNDS).
    // - Sub-grid over available (IOU): a payout a tenth of a unit above the available assets is
    //   rejected (tecINSUFFICIENT_FUNDS) by the check on the unclamped payout. Each cusp pays
    //   exactly the available assets.
    // - Decade crossing (IOU): the payout is truncated to the grid of available - amount, ten
    //   units from 10^16 units up, so there a one-unit withdrawal truncates to zero
    //   (tecPRECISION_LOSS). Each cusp leaves exactly 10^16 - 1 or 10^16 units.
    // - Holder shares: redeeming more shares than the holder owns is rejected
    //   (tecINSUFFICIENT_FUNDS). Each cusp redeems exactly the shares held.
    // - Loss waiver: a holder of every share redeems at the assets total, any other at assets
    //   total - loss unrealized. Every row succeeds; it shows in the payout.
    // - Share overflow (XRP, MPT): an amount worth more than 2^63 - 1 shares fails the share
    //   computation (tecPATH_DRY). Each cusp converts to exactly 2^63 - 1 shares.
    // clang-format off
    static constexpr WithdrawCase kZeroSharesByAssets[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1, amount 1'000'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'998, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 999'999'999, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 1'000'000'000, .expected = tesSUCCESS},
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
    static constexpr WithdrawCase kZeroSharesByAssetsIntegral[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tesSUCCESS},
    };
    static constexpr WithdrawCase kZeroSharesByAssetsIou[] = {
        // total 2, sharesTotal 1, amount 2
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        // total 2, sharesTotal 2, amount 1
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS},
        // total 1'000'000'000, sharesTotal 1'000'000'000, amount 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS},
    };
    // FV_M2_3 (C++ behaviour pinned as expected): the payout rounds to nearest.
    static constexpr WithdrawCase kZeroPayout[] = {
        // nav 1, sharesTotal 2, shares 1
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 4}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 4}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // nav 1, sharesTotal 2'000'000'000, shares 1'000'000'000
        {.vault = {.available = 1, .sharesTotal = 1'999'999'998}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'998}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'999}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'999}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'000}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'000}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'001}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'001}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'002}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'002}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'001, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        // nav 1'000'000'000, sharesTotal 2'000'000'000, shares 1
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'999'999'998}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'999'999'999}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'000}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'001}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2'000'000'002}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // nav 31'250, sharesTotal 2'000'000'000, shares 32'000
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'998}, .amount = 31'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'998}, .amount = 31'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'998}, .amount = 32'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'998}, .amount = 32'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'998}, .amount = 32'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'999}, .amount = 31'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'999}, .amount = 31'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'999}, .amount = 32'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'999}, .amount = 32'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 1'999'999'999}, .amount = 32'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'000}, .amount = 31'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'000}, .amount = 31'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'000}, .amount = 32'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'000}, .amount = 32'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'000}, .amount = 32'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'001}, .amount = 31'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'001}, .amount = 31'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'001}, .amount = 32'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'001}, .amount = 32'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'001}, .amount = 32'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'002}, .amount = 31'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'002}, .amount = 31'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'002}, .amount = 32'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'002}, .amount = 32'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 31'250, .sharesTotal = 2'000'000'002}, .amount = 32'002, .expected = tesSUCCESS, .byShares = true},
        // nav 1, sharesTotal 9'223'372'036'854'775'804, shares 4'611'686'018'427'387'902
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'802}, .amount = 4'611'686'018'427'387'900, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'802}, .amount = 4'611'686'018'427'387'901, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'802}, .amount = 4'611'686'018'427'387'902, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'802}, .amount = 4'611'686'018'427'387'903, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'802}, .amount = 4'611'686'018'427'387'904, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'803}, .amount = 4'611'686'018'427'387'900, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'803}, .amount = 4'611'686'018'427'387'901, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'803}, .amount = 4'611'686'018'427'387'902, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'803}, .amount = 4'611'686'018'427'387'903, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'803}, .amount = 4'611'686'018'427'387'904, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'804}, .amount = 4'611'686'018'427'387'900, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'804}, .amount = 4'611'686'018'427'387'901, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'804}, .amount = 4'611'686'018'427'387'902, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'804}, .amount = 4'611'686'018'427'387'903, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'804}, .amount = 4'611'686'018'427'387'904, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'805}, .amount = 4'611'686'018'427'387'900, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'805}, .amount = 4'611'686'018'427'387'901, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'805}, .amount = 4'611'686'018'427'387'902, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'805}, .amount = 4'611'686'018'427'387'903, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'805}, .amount = 4'611'686'018'427'387'904, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'806}, .amount = 4'611'686'018'427'387'900, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'806}, .amount = 4'611'686'018'427'387'901, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'806}, .amount = 4'611'686'018'427'387'902, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'806}, .amount = 4'611'686'018'427'387'903, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 9'223'372'036'854'775'806}, .amount = 4'611'686'018'427'387'904, .expected = tesSUCCESS, .byShares = true},
        // nav 100'000'000'000'000'000, sharesTotal 200'000'000'000'000'000, shares 1
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 199'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 199'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 199'999'999'999'999'998}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 199'999'999'999'999'999}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 199'999'999'999'999'999}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 199'999'999'999'999'999}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'000}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'000}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'000}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'001}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'001}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'001}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'002}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'002}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 200'000'000'000'000'002}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // nav 2'147'483'647, sharesTotal 9'223'372'032'559'808'512, shares 2'147'483'648
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'510}, .amount = 2'147'483'646, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'510}, .amount = 2'147'483'647, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'510}, .amount = 2'147'483'648, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'510}, .amount = 2'147'483'649, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'510}, .amount = 2'147'483'650, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'511}, .amount = 2'147'483'646, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'511}, .amount = 2'147'483'647, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'511}, .amount = 2'147'483'648, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'511}, .amount = 2'147'483'649, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'511}, .amount = 2'147'483'650, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'512}, .amount = 2'147'483'646, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'512}, .amount = 2'147'483'647, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'512}, .amount = 2'147'483'648, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'512}, .amount = 2'147'483'649, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'512}, .amount = 2'147'483'650, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'513}, .amount = 2'147'483'646, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'513}, .amount = 2'147'483'647, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'513}, .amount = 2'147'483'648, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'513}, .amount = 2'147'483'649, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'513}, .amount = 2'147'483'650, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'514}, .amount = 2'147'483'646, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'514}, .amount = 2'147'483'647, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'514}, .amount = 2'147'483'648, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'514}, .amount = 2'147'483'649, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'147'483'647, .sharesTotal = 9'223'372'032'559'808'514}, .amount = 2'147'483'650, .expected = tesSUCCESS, .byShares = true},
    };
    static constexpr WithdrawCase kClampToZero[] = {
        // nav 2, sharesTotal 2, shares 1
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 4}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // nav 2, sharesTotal 2'000'000'000, shares 1'000'000'000
        {.vault = {.available = 2, .sharesTotal = 1'999'999'998}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'998}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'998}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'999}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'999}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1'999'999'999}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'000}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'000}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'000}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'001}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'001}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'001}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'002}, .amount = 999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'002}, .amount = 999'999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        // nav 1'000'000'000, sharesTotal 10'000'000'000, shares 10
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'998}, .amount = 8, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'998}, .amount = 9, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'998}, .amount = 10, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'998}, .amount = 11, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'998}, .amount = 12, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'999}, .amount = 8, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'999}, .amount = 9, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'999}, .amount = 10, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'999}, .amount = 11, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 9'999'999'999}, .amount = 12, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'000}, .amount = 8, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'000}, .amount = 9, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'000}, .amount = 10, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'000}, .amount = 11, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'000}, .amount = 12, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'001}, .amount = 8, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'001}, .amount = 9, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'001}, .amount = 10, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'001}, .amount = 11, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'001}, .amount = 12, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'002}, .amount = 8, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'002}, .amount = 9, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'002}, .amount = 10, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'002}, .amount = 11, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'002}, .amount = 12, .expected = tesSUCCESS, .byShares = true},
        // nav 1'000'000'000, sharesTotal 1'000'000'000'000'000, shares 1'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'998}, .amount = 999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'998}, .amount = 999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'998}, .amount = 1'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'998}, .amount = 1'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'998}, .amount = 1'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'999}, .amount = 999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'999}, .amount = 999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'999}, .amount = 1'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'999}, .amount = 1'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999'999'999}, .amount = 1'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'000}, .amount = 999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'000}, .amount = 999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'000}, .amount = 1'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'000}, .amount = 1'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'000}, .amount = 1'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'001}, .amount = 999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'001}, .amount = 999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'001}, .amount = 1'000'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'001}, .amount = 1'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'001}, .amount = 1'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'002}, .amount = 999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'002}, .amount = 999'999, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'002}, .amount = 1'000'000, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'002}, .amount = 1'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000'000'002}, .amount = 1'000'002, .expected = tesSUCCESS, .byShares = true},
        // nav 4'999'999'999'999'998, sharesTotal 9'999'999'999'999'996, shares 2
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'994}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'994}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'994}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'994}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'995}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'995}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'995}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'995}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'996}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'996}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'996}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'996}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'997}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'997}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'997}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'997}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        // nav 2, sharesTotal 9'999'999'999'999'996, shares 4'999'999'999'999'998
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'996, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'994}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'996, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'997, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'995}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'996, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'997, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'996}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'996, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'997, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'997}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'996, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'997, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'998, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 9'999'999'999'999'998}, .amount = 5'000'000'000'000'000, .expected = tesSUCCESS, .byShares = true},
    };
    // Gap 16 (C++ defect pinned as expected): the tefEXCEPTION rows; a C++ fix returns a tec.
    static constexpr WithdrawCase kXrpPayoutRange[] = {
        // nav 1, sharesTotal 1, shares 100'000'000'000'000'000
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 99'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 99'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 100'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 100'000'000'000'000'001, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1, .sharesTotal = 1}, .amount = 100'000'000'000'000'002, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1, .sharesTotal = 2}, .amount = 99'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2}, .amount = 99'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2}, .amount = 100'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2}, .amount = 100'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 2}, .amount = 100'000'000'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 99'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 99'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 100'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 100'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 3}, .amount = 100'000'000'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // nav 1'000'000'000, sharesTotal 1'000'000'000, shares 100'000'000'000'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 99'999'999'999'999'998, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 99'999'999'999'999'999, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 100'000'000'000'000'000, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 100'000'000'000'000'001, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'998}, .amount = 100'000'000'000'000'002, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 99'999'999'999'999'998, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 99'999'999'999'999'999, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 100'000'000'000'000'000, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 100'000'000'000'000'001, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 999'999'999}, .amount = 100'000'000'000'000'002, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 99'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 99'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 100'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 100'000'000'000'000'001, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 100'000'000'000'000'002, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 99'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 99'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 100'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 100'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'001}, .amount = 100'000'000'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 99'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 99'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 100'000'000'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 100'000'000'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'002}, .amount = 100'000'000'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // nav 1'000'000'000, sharesTotal 1, shares 100'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 99'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 99'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 100'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 100'000'001, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1}, .amount = 100'000'002, .expected = tefEXCEPTION, .byShares = true, .leanError = LeanError::outOfRange},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 99'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 99'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 100'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 100'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 2}, .amount = 100'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 99'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 99'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 100'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 100'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 3}, .amount = 100'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
    };
    static constexpr WithdrawCase kMptPayoutRange[] = {
        // nav 2, sharesTotal 1, shares 4'611'686'018'427'387'903
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 4'611'686'018'427'387'901, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 4'611'686'018'427'387'902, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 4'611'686'018'427'387'903, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 4'611'686'018'427'387'904, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 1}, .amount = 4'611'686'018'427'387'905, .expected = tecPATH_DRY, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 4'611'686'018'427'387'901, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 4'611'686'018'427'387'902, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 4'611'686'018'427'387'903, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 4'611'686'018'427'387'904, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 4'611'686'018'427'387'905, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 4'611'686'018'427'387'901, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 4'611'686'018'427'387'902, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 4'611'686'018'427'387'903, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 4'611'686'018'427'387'904, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 3}, .amount = 4'611'686'018'427'387'905, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
    };
    static constexpr WithdrawCase kIouPayoutRange[] = {
        // nav 9'999'999'999'999'999, sharesTotal 1, shares 1, nav at exponent 80
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1}, .amount = 1, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1}, .amount = 2, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1}, .amount = 3, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 2}, .amount = 3, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 3}, .amount = 3, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        // nav 9'999'999'999'999'999, sharesTotal 1'000'000'000, shares 1'000'000'000, nav at exponent 80
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'998}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'998}, .amount = 999'999'999, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'998}, .amount = 1'000'000'000, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'998}, .amount = 1'000'000'001, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'998}, .amount = 1'000'000'002, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'999}, .amount = 1'000'000'000, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'999}, .amount = 1'000'000'001, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 999'999'999}, .amount = 1'000'000'002, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'002, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'002}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        // nav 9'999'999'999'999'999, sharesTotal 9'999'999'999'999'999, shares 9'999'999'999'999'999, nav at exponent 80
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'998, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'999, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 10'000'000'000'000'000, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'997}, .amount = 10'000'000'000'000'001, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'999, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 10'000'000'000'000'000, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'998}, .amount = 10'000'000'000'000'001, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 10'000'000'000'000'000, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .amount = 10'000'000'000'000'001, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000}, .amount = 9'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000}, .amount = 10'000'000'000'000'000, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000}, .amount = 10'000'000'000'000'001, .expected = tecPATH_DRY, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'001}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'001}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'001}, .amount = 9'999'999'999'999'999, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'001}, .amount = 10'000'000'000'000'000, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 10'000'000'000'000'001}, .amount = 10'000'000'000'000'001, .expected = tesSUCCESS, .byShares = true, .availableExponent = 80},
    };
    // FV_M2_3 (C++ behaviour pinned as expected): the payout rounds to nearest.
    static constexpr WithdrawCase kToNearest[] = {
        // nav 1'999'999'999'999'999, sharesTotal 2, shares 1
        {.vault = {.available = 1'999'999'999'999'997, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'999'999'999'999'997, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'999'999'999'999'998, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'999'999'999'999'998, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'999'999'999'999'999, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'999'999'999'999'999, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'000, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'000, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'001, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'001, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        // nav 2'000'000'000'000'001, sharesTotal 2, shares 1
        {.vault = {.available = 1'999'999'999'999'999, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'999'999'999'999'999, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'000, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'000, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'001, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'001, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'002, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'002, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'003, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'003, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        // nav 2'000'000'000'000'003, sharesTotal 2, shares 1
        {.vault = {.available = 2'000'000'000'000'001, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'001, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'002, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'002, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'003, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'003, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'004, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'004, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'005, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2'000'000'000'000'005, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        // nav 9'999'999'999'999'997, sharesTotal 2, shares 1
        {.vault = {.available = 9'999'999'999'999'995, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'995, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'996, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'996, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
    };
    static constexpr WithdrawCase kAvailable[] = {
        // available 1, deployed 5, amount 1
        {.vault = {.deployed = 5, .sharesTotal = 5, .holderShares = 4}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.deployed = 5, .sharesTotal = 5, .holderShares = 4}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.deployed = 5, .sharesTotal = 5, .holderShares = 4}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .deployed = 5, .sharesTotal = 6, .holderShares = 5}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 5, .sharesTotal = 6, .holderShares = 5}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .deployed = 5, .sharesTotal = 6, .holderShares = 5}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2, .deployed = 5, .sharesTotal = 7, .holderShares = 6}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 5, .sharesTotal = 7, .holderShares = 6}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 5, .sharesTotal = 7, .holderShares = 6}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 3, .deployed = 5, .sharesTotal = 8, .holderShares = 7}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 5, .sharesTotal = 8, .holderShares = 7}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 5, .sharesTotal = 8, .holderShares = 7}, .amount = 3, .expected = tesSUCCESS},
        // available 1, deployed 9'999'999'999'999'996, amount 1
        {.vault = {.deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 3, .expected = tesSUCCESS},
        // available 1'000'000'000, deployed 5, amount 1'000'000'000
        {.vault = {.available = 999'999'998, .deployed = 5, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 5, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'998, .deployed = 5, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'998, .deployed = 5, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'998, .deployed = 5, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'999, .deployed = 5, .sharesTotal = 1'000'000'004, .holderShares = 1'000'000'003}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 5, .sharesTotal = 1'000'000'004, .holderShares = 1'000'000'003}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 5, .sharesTotal = 1'000'000'004, .holderShares = 1'000'000'003}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'999, .deployed = 5, .sharesTotal = 1'000'000'004, .holderShares = 1'000'000'003}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'999, .deployed = 5, .sharesTotal = 1'000'000'004, .holderShares = 1'000'000'003}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'005, .holderShares = 1'000'000'004}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'005, .holderShares = 1'000'000'004}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'005, .holderShares = 1'000'000'004}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'005, .holderShares = 1'000'000'004}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'000, .deployed = 5, .sharesTotal = 1'000'000'005, .holderShares = 1'000'000'004}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .deployed = 5, .sharesTotal = 1'000'000'006, .holderShares = 1'000'000'005}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 5, .sharesTotal = 1'000'000'006, .holderShares = 1'000'000'005}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 5, .sharesTotal = 1'000'000'006, .holderShares = 1'000'000'005}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 5, .sharesTotal = 1'000'000'006, .holderShares = 1'000'000'005}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 5, .sharesTotal = 1'000'000'006, .holderShares = 1'000'000'005}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'002, .deployed = 5, .sharesTotal = 1'000'000'007, .holderShares = 1'000'000'006}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 5, .sharesTotal = 1'000'000'007, .holderShares = 1'000'000'006}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 5, .sharesTotal = 1'000'000'007, .holderShares = 1'000'000'006}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 5, .sharesTotal = 1'000'000'007, .holderShares = 1'000'000'006}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 5, .sharesTotal = 1'000'000'007, .holderShares = 1'000'000'006}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // available 1'000'000'000, deployed 1'000'000'000, amount 1'000'000'000
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998, .holderShares = 1'999'999'997}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998, .holderShares = 1'999'999'997}, .amount = 999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998, .holderShares = 1'999'999'997}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998, .holderShares = 1'999'999'997}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'998, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'998, .holderShares = 1'999'999'997}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999, .holderShares = 1'999'999'998}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999, .holderShares = 1'999'999'998}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999, .holderShares = 1'999'999'998}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999, .holderShares = 1'999'999'998}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 999'999'999, .deployed = 1'000'000'000, .sharesTotal = 1'999'999'999, .holderShares = 1'999'999'998}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'000, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001, .holderShares = 2'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001, .holderShares = 2'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001, .holderShares = 2'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001, .holderShares = 2'000'000'000}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'001, .holderShares = 2'000'000'000}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .deployed = 1'000'000'000, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001}, .amount = 1'000'000'002, .expected = tesSUCCESS},
        // available 9'999'999'999'999'992, deployed 5, amount 9'999'999'999'999'992
        {.vault = {.available = 9'999'999'999'999'990, .deployed = 5, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'990, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .deployed = 5, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'991, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'990, .deployed = 5, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'992, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'990, .deployed = 5, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'993, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'990, .deployed = 5, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'994, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'991, .deployed = 5, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'990, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'991, .deployed = 5, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'991, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'991, .deployed = 5, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'992, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'991, .deployed = 5, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'993, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'991, .deployed = 5, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'994, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'992, .deployed = 5, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'990, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'992, .deployed = 5, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'991, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'992, .deployed = 5, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'992, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'992, .deployed = 5, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'993, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'992, .deployed = 5, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'994, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'993, .deployed = 5, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'990, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'993, .deployed = 5, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'991, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'993, .deployed = 5, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'992, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'993, .deployed = 5, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'993, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'993, .deployed = 5, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'994, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 5, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'990, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 5, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'991, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 5, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'992, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 5, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'993, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'994, .deployed = 5, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS},
        // available 4'999'999'999'999'997, deployed 5'000'000'000'000'000, amount 4'999'999'999'999'997
        {.vault = {.available = 4'999'999'999'999'995, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'995, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'996, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'995, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'997, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'995, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'995, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 4'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'997, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'996, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 4'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 4'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 4'999'999'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'995, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'996, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 4'999'999'999'999'999, .expected = tesSUCCESS},
    };
    static constexpr WithdrawCase kFinal[] = {
        // available 2, deployed 0, shares 2
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .amount = 3, .expected = tecHAS_OBLIGATIONS, .byShares = true},
        {.vault = {.available = 2, .deployed = 2, .sharesTotal = 4}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .deployed = 2, .sharesTotal = 4}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .deployed = 2, .sharesTotal = 4}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .deployed = 2, .sharesTotal = 4}, .amount = 4, .expected = tecHAS_OBLIGATIONS, .byShares = true},
        // available 1'000'000'000, deployed 0, shares 1'000'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .amount = 1'000'000'001, .expected = tecHAS_OBLIGATIONS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 1'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 1'000'000'002}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 1'000'000'002}, .amount = 1'000'000'002, .expected = tecHAS_OBLIGATIONS, .byShares = true},
        // available 9'999'999'999'999'997, deployed 0, shares 9'999'999'999'999'997
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'998, .expected = tecHAS_OBLIGATIONS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 2, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 2, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 2, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 2, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 2, .sharesTotal = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'999, .expected = tecHAS_OBLIGATIONS, .byShares = true},
    };
    // Known C++ defect pinned as expected (no finding id): shares burned for a zero payout.
    static constexpr WithdrawCase kImpaired[] = {
        // deployed 2, loss 2, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 2, .loss = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // deployed 9'999'999'999'999'999, loss 9'999'999'999'999'999, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 9'223'372'036'854'775'807, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 2, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 2, .holderShares = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 1'000'000'000, .sharesTotal = 2, .holderShares = 1}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
    };
    static constexpr WithdrawCase kImpairedIntegral[] = {
        // deployed 2, loss 2, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 1, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 1, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 1, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        // deployed 9'999'999'999'999'999, loss 9'999'999'999'999'999, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'997, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'997, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'997, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 9'223'372'036'854'775'807, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 2, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 3, .expected = tecPRECISION_LOSS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 2, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 2, .holderShares = 1}, .amount = 1, .expected = tecPRECISION_LOSS, .byShares = true},
    };
    static constexpr WithdrawCase kImpairedIou[] = {
        // deployed 2, loss 2, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 2, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 1, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 1, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 2, .loss = 1, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // deployed 9'999'999'999'999'999, loss 9'999'999'999'999'999, sharesTotal 1'000'000'000, shares 1
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'997, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'997, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'997, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 9'999'999'999'999'999, .loss = 9'999'999'999'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 9'223'372'036'854'775'807, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'998, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 9'223'372'036'854'775'807, .holderShares = 9'223'372'036'854'775'806}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // deployed 1'000'000'000, loss 1'000'000'000, sharesTotal 2, shares 1
        {.vault = {.deployed = 1'000'000'000, .loss = 999'999'999, .sharesTotal = 2, .holderShares = 1}, .amount = 1, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
    };
    static constexpr WithdrawCase kSubGridOverAvailable[] = {
        // available 1, deployed 1, sharesTotal 20, shares 10
        {.vault = {.available = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 8, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 9, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 10, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 11, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 12, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 8, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 9, .expected = tecPRECISION_LOSS, .byShares = true},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 10, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 11, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 20, .holderShares = 19}, .amount = 12, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 2, .sharesTotal = 20, .holderShares = 19}, .amount = 8, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 2, .sharesTotal = 20, .holderShares = 19}, .amount = 9, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 2, .sharesTotal = 20, .holderShares = 19}, .amount = 10, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 2, .sharesTotal = 20, .holderShares = 19}, .amount = 11, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 2, .sharesTotal = 20, .holderShares = 19}, .amount = 12, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 3, .sharesTotal = 20, .holderShares = 19}, .amount = 8, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 3, .sharesTotal = 20, .holderShares = 19}, .amount = 9, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 3, .sharesTotal = 20, .holderShares = 19}, .amount = 10, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 3, .sharesTotal = 20, .holderShares = 19}, .amount = 11, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1, .deployed = 3, .sharesTotal = 20, .holderShares = 19}, .amount = 12, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // available 1'000'000'000, deployed 1, sharesTotal 10'000'000'010, shares 10'000'000'000
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'002, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 2, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 3, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 3, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 9'999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 3, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 3, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .deployed = 3, .sharesTotal = 10'000'000'010, .holderShares = 10'000'000'009}, .amount = 10'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        // available 999'999'999'999'999, deployed 1, sharesTotal 10'000'000'000'000'000, shares 9'999'999'999'999'990
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'988, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'989, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'990, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'991, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'992, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 1, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'988, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 1, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'989, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 1, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'990, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 1, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'991, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 1, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'992, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 2, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'988, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 2, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'989, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 2, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'990, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 2, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'991, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 2, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'992, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 3, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'988, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 3, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'989, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 3, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'990, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 3, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'991, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999'999'999, .deployed = 3, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9'999'999'999'999'992, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
    };
    static constexpr WithdrawCase kDecade[] = {
        // available 10'000'000'000'000'000, amount 1
        {.vault = {.available = 9'999'999'999'999'980, .sharesTotal = 9'999'999'999'999'980, .holderShares = 9'999'999'999'999'979}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'980, .sharesTotal = 9'999'999'999'999'980, .holderShares = 9'999'999'999'999'979}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'980, .sharesTotal = 9'999'999'999'999'980, .holderShares = 9'999'999'999'999'979}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 1, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 2, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 3, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 2, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 3, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 1, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 2, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 3, .expected = tecPRECISION_LOSS},
        // available 10'000'000'000'000'010, amount 10
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 8, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 9, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 10, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 11, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'990, .sharesTotal = 9'999'999'999'999'990, .holderShares = 9'999'999'999'999'989}, .amount = 12, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 8, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 9, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 10, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 11, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'000, .sharesTotal = 10'000'000'000'000'000, .holderShares = 9'999'999'999'999'999}, .amount = 12, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 8, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 9, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 10, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 11, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'010, .sharesTotal = 10'000'000'000'000'010, .holderShares = 10'000'000'000'000'009}, .amount = 12, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 8, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 9, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 10, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 11, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'020, .sharesTotal = 10'000'000'000'000'020, .holderShares = 10'000'000'000'000'019}, .amount = 12, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'030, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 8, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'030, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 9, .expected = tecPRECISION_LOSS},
        {.vault = {.available = 10'000'000'000'000'030, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 10, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'030, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 11, .expected = tesSUCCESS},
        {.vault = {.available = 10'000'000'000'000'030, .sharesTotal = 10'000'000'000'000'030, .holderShares = 10'000'000'000'000'029}, .amount = 12, .expected = tesSUCCESS},
    };
    static constexpr WithdrawCase kHolderShares[] = {
        // holderShares 1, shares 1
        {.vault = {.available = 2, .sharesTotal = 2, .holderShares = 1}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2, .holderShares = 1}, .amount = 2, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 2, .sharesTotal = 2, .holderShares = 1}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 3, .sharesTotal = 3, .holderShares = 2}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 3, .sharesTotal = 3, .holderShares = 2}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 3, .sharesTotal = 3, .holderShares = 2}, .amount = 3, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 4, .sharesTotal = 4, .holderShares = 3}, .amount = 1, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .sharesTotal = 4, .holderShares = 3}, .amount = 2, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .sharesTotal = 4, .holderShares = 3}, .amount = 3, .expected = tesSUCCESS, .byShares = true},
        // holderShares 1'000'000'000, shares 1'000'000'000
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999, .holderShares = 999'999'998}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999, .holderShares = 999'999'998}, .amount = 999'999'999, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999, .holderShares = 999'999'998}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999, .holderShares = 999'999'998}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999, .holderShares = 999'999'998}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000'000'000, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 1'000'000'001, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001, .holderShares = 1'000'000'000}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002, .holderShares = 1'000'000'001}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002, .holderShares = 1'000'000'001}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002, .holderShares = 1'000'000'001}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002, .holderShares = 1'000'000'001}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002, .holderShares = 1'000'000'001}, .amount = 1'000'000'002, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 1'000'000'003, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 999'999'998, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'003, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 999'999'999, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'003, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 1'000'000'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'003, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 1'000'000'001, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 1'000'000'003, .sharesTotal = 1'000'000'003, .holderShares = 1'000'000'002}, .amount = 1'000'000'002, .expected = tesSUCCESS, .byShares = true},
        // holderShares 9'999'999'999'999'996, shares 9'999'999'999'999'996
        {.vault = {.available = 9'999'999'999'999'995, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'995, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'995, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'995, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'996, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'995, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'997, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'995, .sharesTotal = 9'999'999'999'999'995, .holderShares = 9'999'999'999'999'994}, .amount = 9'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'996, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'997, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'996, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 9'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'997, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997, .holderShares = 9'999'999'999'999'996}, .amount = 9'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998, .holderShares = 9'999'999'999'999'997}, .amount = 9'999'999'999'999'998, .expected = tecINSUFFICIENT_FUNDS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'994, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'995, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'996, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'997, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999, .holderShares = 9'999'999'999'999'998}, .amount = 9'999'999'999'999'998, .expected = tesSUCCESS, .byShares = true},
    };
    static constexpr WithdrawCase kWaiver[] = {
        // total 8, deployed 4, loss 2, holderShares 8, shares 4
        {.vault = {.available = 4, .deployed = 4, .sharesTotal = 8, .holderShares = 6}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 1, .sharesTotal = 8, .holderShares = 6}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 2, .sharesTotal = 8, .holderShares = 6}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 3, .sharesTotal = 8, .holderShares = 6}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 4, .sharesTotal = 8, .holderShares = 6}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .sharesTotal = 8, .holderShares = 7}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 1, .sharesTotal = 8, .holderShares = 7}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 2, .sharesTotal = 8, .holderShares = 7}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 3, .sharesTotal = 8, .holderShares = 7}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 4, .sharesTotal = 8, .holderShares = 7}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .sharesTotal = 8, .holderShares = 8}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 1, .sharesTotal = 8, .holderShares = 8}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 2, .sharesTotal = 8, .holderShares = 8}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 3, .sharesTotal = 8, .holderShares = 8}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4, .deployed = 4, .loss = 4, .sharesTotal = 8, .holderShares = 8}, .amount = 4, .expected = tesSUCCESS, .byShares = true},
        // total 1'000'000'000, deployed 500'000'000, loss 250'000'000, holderShares 1'000'000'000, shares 1'000
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'001, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'002, .sharesTotal = 1'000'000'000, .holderShares = 999'999'998}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'998, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'999, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'000, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'001, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'002, .sharesTotal = 1'000'000'000, .holderShares = 999'999'999}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'998, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 249'999'999, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'000, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'001, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .loss = 250'000'002, .sharesTotal = 1'000'000'000, .holderShares = 1'000'000'000}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        // total 9'999'999'999'999'996, deployed 4'999'999'999'999'998, loss 2'499'999'999'999'999, holderShares 9'999'999'999'999'996, shares 1'000
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'997, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'998, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'999, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'001, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'994}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'997, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'998, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'999, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'001, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'995}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'997, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'998, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'499'999'999'999'999, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'000, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 4'999'999'999'999'998, .loss = 2'500'000'000'000'001, .sharesTotal = 9'999'999'999'999'996, .holderShares = 9'999'999'999'999'996}, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
    };
    static constexpr WithdrawCase kShareOverflow[] = {
        // nav 1, sharesTotal 1'317'624'576'693'539'401, amount 7
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 5, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 6, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 7, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'399}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 5, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 6, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 7, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'400}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 5, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 6, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 7, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'401}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 5, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 6, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 7, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'402}, .amount = 9, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 5, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 6, .expected = tecINSUFFICIENT_FUNDS},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 7, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 8, .expected = tecPATH_DRY},
        {.vault = {.available = 1, .sharesTotal = 1'317'624'576'693'539'403}, .amount = 9, .expected = tecPATH_DRY},
    };
    // clang-format on

    // Runs every list on the vaults staged open-ended or, when `closed`, closed-ended in
    // Subscription without a fee field: outside Investment no phase check rejects and no fee is
    // charged, so withdraw behaves as on an open-ended vault.
    void
    runWithdrawBoundaries(jtx::Env& env, Setup const& s, bool closed)
    {
        std::uint32_t const p = parentCloseTime(env);
        auto const run = [&](std::string const& name,
                             TestVaults const& vaults,
                             std::span<WithdrawCase const> cases) {
            for (auto const& [vault, holder] : vaults)
            {
                beginCase(("withdraw " + vaultName(env, vault) + " " + name +
                           (closed ? ", closed-ended" : ""))
                              .c_str());
                Asset const asset = env.le(vault)->at(sfAsset);
                for (auto const& [row, amount, expected, byShares, availableExponent, leanError] :
                     cases)
                {
                    StagedVault staged = row;
                    if (closed)
                    {
                        staged.subscriptionDate = p + 1'000;
                        staged.redemptionDate = p + 1'001'000;
                    }
                    STAmount const withdrawal = byShares ? STAmount{shareIssue(env, vault), amount}
                                                         : vaultUnits(env, vault, amount);
                    StagedAmounts amounts = stagedAmounts(env, vault, staged);
                    std::string at = sampleText(staged, withdrawal);
                    if (availableExponent)
                    {
                        amounts.available = STAmount{
                            asset, static_cast<std::uint64_t>(row.available), *availableExponent};
                        at += "available at exponent " + std::to_string(*availableExponent) + ": ";
                    }
                    AppliedVaultTx const cpp =
                        applyWithdraw(env, vault, holder, amounts, withdrawal);
                    LeanVaultResult const lean =
                        leanWithdraw(cpp, amounts, withdrawal, byShares, p);
                    if (leanError)
                        expectSame(*this, at, cpp, lean, expected, leanError);
                    else
                        expectSame(*this, at, cpp, lean, expected);
                }
            }
        };
        // An IOU list again with the non-issuer holder, which C++ pays over a trust line.
        auto const runIou = [&](std::string const& name,
                                TestVaults const& vaults,
                                std::span<WithdrawCase const> cases) {
            run(name, vaults, cases);
            run(name + ", non-issuer", s.iouHolder, cases);
        };

        runIou("zero shares by assets", s.all, kZeroSharesByAssets);
        run("zero shares by assets", s.integral, kZeroSharesByAssetsIntegral);
        runIou("zero shares by assets", s.ious, kZeroSharesByAssetsIou);
        run("zero payout", s.integral, kZeroPayout);
        runIou("clamp to zero", s.ious, kClampToZero);
        run("payout range", s.xrp, kXrpPayoutRange);
        run("payout range", s.mpt, kMptPayoutRange);
        runIou("payout range", s.ious, kIouPayoutRange);
        runIou("to nearest", s.ious, kToNearest);
        runIou("available", s.all, kAvailable);
        runIou("final", s.all, kFinal);
        runIou("fully impaired", s.all, kImpaired);
        run("fully impaired", s.integral, kImpairedIntegral);
        runIou("fully impaired", s.ious, kImpairedIou);
        runIou("sub-grid over available", s.ious, kSubGridOverAvailable);
        runIou("decade crossing", s.ious, kDecade);
        runIou("holder shares", s.all, kHolderShares);
        runIou("loss waiver", s.all, kWaiver);
        run("share overflow", s.integral, kShareOverflow);
    }

    void
    testWithdrawBoundaries(jtx::Env& env, Setup const& s)
    {
        runWithdrawBoundaries(env, s, false);
    }

    // The same lists in Subscription, then the lists that only exist for a closed-ended vault: the
    // phase dates and the early-exit fee. Their rows put the subscription date at P + subscription
    // and the redemption date at P + redemption (P the parent close time); the fee rate is the
    // vault's earlyExitFeeRate.
    // - Subscription end: without a fee field, withdrawing one unit is accepted while
    //   P <= subscription date and tecTOO_SOON in Investment.
    // - Redemption start: without a fee field, tecTOO_SOON up to P = redemption date - 1, accepted
    //   from P = redemption date.
    // - Fee phase: with a fee rate the vault never refuses; the fee is charged only in Investment,
    //   so the payout changes at both dates.
    // - Full fee dust: with a 100% fee no clamp runs, so a debit too small to change the stored
    //   available assets is rejected (tecPRECISION_LOSS) by that check alone. Each cusp debits
    //   exactly half the last stored digit.
    // - Fee consumes payout: the payout gross - fee (fee rounded up, payout down) must be at least
    //   one unit (tecPRECISION_LOSS below); a 100% rate pays nothing and succeeds. Each cusp pays
    //   exactly one unit.
    // - Net over available: with a fee only the net payout must be available
    //   (tecINSUFFICIENT_FUNDS above). Each cusp nets exactly the available assets, at price 1.
    void
    testClosedEndedWithdrawBoundaries(jtx::Env& env, Setup const& s)
    {
        runWithdrawBoundaries(env, s, true);

        struct DateCase
        {
            StagedVault vault;
            std::int64_t subscription;
            std::int64_t redemption;
            std::int64_t amount;
            TER expected;
            bool byShares{};
        };
        // clang-format off
        static constexpr DateCase kSubscriptionEnd[] = {
            // gap 180, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -2, .redemption = 178, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -1, .redemption = 179, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 0, .redemption = 180, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 1, .redemption = 181, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 2, .redemption = 182, .amount = 1, .expected = tesSUCCESS},
            // gap 1'000'000, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -2, .redemption = 999'998, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -1, .redemption = 999'999, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 0, .redemption = 1'000'000, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 1, .redemption = 1'000'001, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 2, .redemption = 1'000'002, .amount = 1, .expected = tesSUCCESS},
            // gap 946'708'559, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -2, .redemption = 946'708'557, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -1, .redemption = 946'708'558, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 0, .redemption = 946'708'559, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 1, .redemption = 946'708'560, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = 2, .redemption = 946'708'561, .amount = 1, .expected = tesSUCCESS},
        };
        static constexpr DateCase kRedemptionStart[] = {
            // gap 180, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -182, .redemption = -2, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -181, .redemption = -1, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -180, .redemption = 0, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -179, .redemption = 1, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -178, .redemption = 2, .amount = 1, .expected = tecTOO_SOON},
            // gap 1'000'000, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -1'000'002, .redemption = -2, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -1'000'001, .redemption = -1, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -1'000'000, .redemption = 0, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -999'999, .redemption = 1, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -999'998, .redemption = 2, .amount = 1, .expected = tecTOO_SOON},
            // gap 946'708'559, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -946'708'561, .redemption = -2, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -946'708'560, .redemption = -1, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -946'708'559, .redemption = 0, .amount = 1, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -946'708'558, .redemption = 1, .amount = 1, .expected = tecTOO_SOON},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999}, .subscription = -946'708'557, .redemption = 2, .amount = 1, .expected = tecTOO_SOON},
        };
        static constexpr DateCase kFeePhase[] = {
            // rate 1, gap 180, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -2, .redemption = 178, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -1, .redemption = 179, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 0, .redemption = 180, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 1, .redemption = 181, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 2, .redemption = 182, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 1, gap 1'000'000, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -2, .redemption = 999'998, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -1, .redemption = 999'999, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 0, .redemption = 1'000'000, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 1, .redemption = 1'000'001, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 2, .redemption = 1'000'002, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 1, gap 946'708'559, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -2, .redemption = 946'708'557, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -1, .redemption = 946'708'558, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 0, .redemption = 946'708'559, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 1, .redemption = 946'708'560, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = 2, .redemption = 946'708'561, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 5'000, gap 180, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -2, .redemption = 178, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -1, .redemption = 179, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 0, .redemption = 180, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 1, .redemption = 181, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 2, .redemption = 182, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 5'000, gap 1'000'000, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -2, .redemption = 999'998, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -1, .redemption = 999'999, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 0, .redemption = 1'000'000, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 1, .redemption = 1'000'001, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 2, .redemption = 1'000'002, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 5'000, gap 946'708'559, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -2, .redemption = 946'708'557, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -1, .redemption = 946'708'558, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 0, .redemption = 946'708'559, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 1, .redemption = 946'708'560, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = 2, .redemption = 946'708'561, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 100'000, gap 180, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -2, .redemption = 178, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1, .redemption = 179, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 0, .redemption = 180, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 1, .redemption = 181, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 2, .redemption = 182, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 100'000, gap 1'000'000, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -2, .redemption = 999'998, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1, .redemption = 999'999, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 0, .redemption = 1'000'000, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 1, .redemption = 1'000'001, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 2, .redemption = 1'000'002, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 100'000, gap 946'708'559, subscription date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -2, .redemption = 946'708'557, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1, .redemption = 946'708'558, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 0, .redemption = 946'708'559, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 1, .redemption = 946'708'560, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = 2, .redemption = 946'708'561, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 1, gap 180, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -182, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -181, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -180, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -179, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -178, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 1, gap 1'000'000, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -1'000'002, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -1'000'001, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -1'000'000, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -999'999, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -999'998, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 1, gap 946'708'559, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -946'708'561, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -946'708'560, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -946'708'559, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -946'708'558, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 1}, .subscription = -946'708'557, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 5'000, gap 180, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -182, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -181, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -180, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -179, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -178, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 5'000, gap 1'000'000, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -1'000'002, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -1'000'001, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -1'000'000, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -999'999, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -999'998, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 5'000, gap 946'708'559, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -946'708'561, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -946'708'560, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -946'708'559, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -946'708'558, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 5'000}, .subscription = -946'708'557, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 100'000, gap 180, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -182, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -181, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -180, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -179, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -178, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 100'000, gap 1'000'000, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000'002, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000'001, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000'000, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -999'999, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -999'998, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            // rate 100'000, gap 946'708'559, redemption date P + offset
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -946'708'561, .redemption = -2, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -946'708'560, .redemption = -1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -946'708'559, .redemption = 0, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -946'708'558, .redemption = 1, .amount = 1'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 2'000'000'000, .sharesTotal = 2'000'000'000, .holderShares = 1'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -946'708'557, .redemption = 2, .amount = 1'000'000'000, .expected = tesSUCCESS},
        };
        static constexpr DateCase kFullFeeDust[] = {
            // nav 2'000'000'000'000'000'000, sharesTotal 4'000'000'000'000'000'000, shares 1'000
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 3'999'999'999'999'999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'000'000, .sharesTotal = 4'000'000'000'000'000'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            // nav 2'000'000'000'000'001'000, sharesTotal 4'000'000'000'000'002'000, shares 1'000
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'998, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'001'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'000, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'001, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 998, .expected = tecPRECISION_LOSS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 999, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'000, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'001, .expected = tesSUCCESS, .byShares = true},
            {.vault = {.available = 2'000'000'000'000'001'000, .sharesTotal = 4'000'000'000'000'002'002, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'002, .expected = tesSUCCESS, .byShares = true},
        };
        static constexpr DateCase kFeeConsumesPayout[] = {
            // rate 50'000, gross 2
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 3, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 4, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 3, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 49'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 4, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 3, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 4, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 3, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 4, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 3, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 50'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 4, .expected = tesSUCCESS},
            // rate 90'000, gross 10
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 8, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 11, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 12, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 8, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 11, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 89'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 12, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 8, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 11, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 12, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 8, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 11, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 12, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 8, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 11, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 90'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 12, .expected = tesSUCCESS},
            // rate 99'000, gross 100
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 98, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 101, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 102, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 98, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 101, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 98'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 102, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 98, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 101, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 102, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 98, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 101, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'001}, .subscription = -1'000, .redemption = 1'000'000, .amount = 102, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 98, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 101, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'002}, .subscription = -1'000, .redemption = 1'000'000, .amount = 102, .expected = tesSUCCESS},
            // rate 99'990, gross 10'000
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'988}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'988}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'988}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'988}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'988}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'002, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'989}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'989}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'989}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'989}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'989}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'002, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'990}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'998, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'990}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'990}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'990}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'990}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'002, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'991}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'998, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'991}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'991}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'000, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'991}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'001, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'991}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'002, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'992}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'998, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'992}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'992}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'000, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'992}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'001, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'992}, .subscription = -1'000, .redemption = 1'000'000, .amount = 10'002, .expected = tecPRECISION_LOSS},
            // rate 99'999, gross 100'000
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'997}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'997}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'997}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'997}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'997}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'002, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'998}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'002, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'998, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'999, .expected = tecPRECISION_LOSS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 99'999}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'002, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 99'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'000'000, .sharesTotal = 1'000'000, .holderShares = 999'999, .earlyExitFeeRate = 100'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 100'002, .expected = tesSUCCESS},
        };
        static constexpr DateCase kNetOverAvailable[] = {
            // rate 5'000, gross 20, available 19, deployed 5
            {.vault = {.available = 17, .deployed = 5, .sharesTotal = 22, .holderShares = 21, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 18, .expected = tesSUCCESS},
            {.vault = {.available = 18, .deployed = 5, .sharesTotal = 23, .holderShares = 22, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 18, .expected = tesSUCCESS},
            {.vault = {.available = 19, .deployed = 5, .sharesTotal = 24, .holderShares = 23, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 18, .expected = tesSUCCESS},
            {.vault = {.available = 20, .deployed = 5, .sharesTotal = 25, .holderShares = 24, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 18, .expected = tesSUCCESS},
            {.vault = {.available = 21, .deployed = 5, .sharesTotal = 26, .holderShares = 25, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 18, .expected = tesSUCCESS},
            {.vault = {.available = 17, .deployed = 5, .sharesTotal = 22, .holderShares = 21, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 19, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 18, .deployed = 5, .sharesTotal = 23, .holderShares = 22, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 19, .expected = tesSUCCESS},
            {.vault = {.available = 19, .deployed = 5, .sharesTotal = 24, .holderShares = 23, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 19, .expected = tesSUCCESS},
            {.vault = {.available = 20, .deployed = 5, .sharesTotal = 25, .holderShares = 24, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 19, .expected = tesSUCCESS},
            {.vault = {.available = 21, .deployed = 5, .sharesTotal = 26, .holderShares = 25, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 19, .expected = tesSUCCESS},
            {.vault = {.available = 17, .deployed = 5, .sharesTotal = 22, .holderShares = 21, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 20, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 18, .deployed = 5, .sharesTotal = 23, .holderShares = 22, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 20, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 19, .deployed = 5, .sharesTotal = 24, .holderShares = 23, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 20, .expected = tesSUCCESS},
            {.vault = {.available = 20, .deployed = 5, .sharesTotal = 25, .holderShares = 24, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 20, .expected = tesSUCCESS},
            {.vault = {.available = 21, .deployed = 5, .sharesTotal = 26, .holderShares = 25, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 20, .expected = tesSUCCESS},
            {.vault = {.available = 17, .deployed = 5, .sharesTotal = 22, .holderShares = 21, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 21, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 18, .deployed = 5, .sharesTotal = 23, .holderShares = 22, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 21, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 19, .deployed = 5, .sharesTotal = 24, .holderShares = 23, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 21, .expected = tesSUCCESS},
            {.vault = {.available = 20, .deployed = 5, .sharesTotal = 25, .holderShares = 24, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 21, .expected = tesSUCCESS},
            {.vault = {.available = 21, .deployed = 5, .sharesTotal = 26, .holderShares = 25, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 21, .expected = tesSUCCESS},
            {.vault = {.available = 17, .deployed = 5, .sharesTotal = 22, .holderShares = 21, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 22, .expected = tecHAS_OBLIGATIONS},
            {.vault = {.available = 18, .deployed = 5, .sharesTotal = 23, .holderShares = 22, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 22, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 19, .deployed = 5, .sharesTotal = 24, .holderShares = 23, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 22, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 20, .deployed = 5, .sharesTotal = 25, .holderShares = 24, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 22, .expected = tesSUCCESS},
            {.vault = {.available = 21, .deployed = 5, .sharesTotal = 26, .holderShares = 25, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 22, .expected = tesSUCCESS},
            // rate 5'000, gross 2'000'000'000, available 1'900'000'000, deployed 100'000'004
            {.vault = {.available = 1'899'999'998, .deployed = 100'000'004, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'899'999'999, .deployed = 100'000'004, .sharesTotal = 2'000'000'003, .holderShares = 2'000'000'002, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'000, .deployed = 100'000'004, .sharesTotal = 2'000'000'004, .holderShares = 2'000'000'003, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'001, .deployed = 100'000'004, .sharesTotal = 2'000'000'005, .holderShares = 2'000'000'004, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'002, .deployed = 100'000'004, .sharesTotal = 2'000'000'006, .holderShares = 2'000'000'005, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'998, .expected = tesSUCCESS},
            {.vault = {.available = 1'899'999'998, .deployed = 100'000'004, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'999, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 1'899'999'999, .deployed = 100'000'004, .sharesTotal = 2'000'000'003, .holderShares = 2'000'000'002, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'000, .deployed = 100'000'004, .sharesTotal = 2'000'000'004, .holderShares = 2'000'000'003, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'001, .deployed = 100'000'004, .sharesTotal = 2'000'000'005, .holderShares = 2'000'000'004, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'002, .deployed = 100'000'004, .sharesTotal = 2'000'000'006, .holderShares = 2'000'000'005, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 1'999'999'999, .expected = tesSUCCESS},
            {.vault = {.available = 1'899'999'998, .deployed = 100'000'004, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 1'899'999'999, .deployed = 100'000'004, .sharesTotal = 2'000'000'003, .holderShares = 2'000'000'002, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'000, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 1'900'000'000, .deployed = 100'000'004, .sharesTotal = 2'000'000'004, .holderShares = 2'000'000'003, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'001, .deployed = 100'000'004, .sharesTotal = 2'000'000'005, .holderShares = 2'000'000'004, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'002, .deployed = 100'000'004, .sharesTotal = 2'000'000'006, .holderShares = 2'000'000'005, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'000, .expected = tesSUCCESS},
            {.vault = {.available = 1'899'999'998, .deployed = 100'000'004, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 1'899'999'999, .deployed = 100'000'004, .sharesTotal = 2'000'000'003, .holderShares = 2'000'000'002, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'001, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 1'900'000'000, .deployed = 100'000'004, .sharesTotal = 2'000'000'004, .holderShares = 2'000'000'003, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'001, .deployed = 100'000'004, .sharesTotal = 2'000'000'005, .holderShares = 2'000'000'004, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'002, .deployed = 100'000'004, .sharesTotal = 2'000'000'006, .holderShares = 2'000'000'005, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'001, .expected = tesSUCCESS},
            {.vault = {.available = 1'899'999'998, .deployed = 100'000'004, .sharesTotal = 2'000'000'002, .holderShares = 2'000'000'001, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'002, .expected = tecHAS_OBLIGATIONS},
            {.vault = {.available = 1'899'999'999, .deployed = 100'000'004, .sharesTotal = 2'000'000'003, .holderShares = 2'000'000'002, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 1'900'000'000, .deployed = 100'000'004, .sharesTotal = 2'000'000'004, .holderShares = 2'000'000'003, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'002, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 1'900'000'001, .deployed = 100'000'004, .sharesTotal = 2'000'000'005, .holderShares = 2'000'000'004, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'002, .expected = tesSUCCESS},
            {.vault = {.available = 1'900'000'002, .deployed = 100'000'004, .sharesTotal = 2'000'000'006, .holderShares = 2'000'000'005, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 2'000'000'002, .expected = tesSUCCESS},
            // rate 5'000, gross 9'999'999'999'999'980, available 9'499'999'999'999'981, deployed 500'000'000'000'003
            {.vault = {.available = 9'499'999'999'999'979, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'982, .holderShares = 9'999'999'999'999'981, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'978, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'980, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'983, .holderShares = 9'999'999'999'999'982, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'978, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'981, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'984, .holderShares = 9'999'999'999'999'983, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'978, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'982, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'985, .holderShares = 9'999'999'999'999'984, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'978, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'983, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'986, .holderShares = 9'999'999'999'999'985, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'978, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'979, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'982, .holderShares = 9'999'999'999'999'981, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'979, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 9'499'999'999'999'980, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'983, .holderShares = 9'999'999'999'999'982, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'979, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'981, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'984, .holderShares = 9'999'999'999'999'983, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'979, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'982, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'985, .holderShares = 9'999'999'999'999'984, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'979, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'983, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'986, .holderShares = 9'999'999'999'999'985, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'979, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'979, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'982, .holderShares = 9'999'999'999'999'981, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'980, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 9'499'999'999'999'980, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'983, .holderShares = 9'999'999'999'999'982, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'980, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 9'499'999'999'999'981, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'984, .holderShares = 9'999'999'999'999'983, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'980, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'982, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'985, .holderShares = 9'999'999'999'999'984, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'980, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'983, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'986, .holderShares = 9'999'999'999'999'985, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'980, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'979, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'982, .holderShares = 9'999'999'999'999'981, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'981, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 9'499'999'999'999'980, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'983, .holderShares = 9'999'999'999'999'982, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'981, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 9'499'999'999'999'981, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'984, .holderShares = 9'999'999'999'999'983, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'981, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'982, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'985, .holderShares = 9'999'999'999'999'984, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'981, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'983, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'986, .holderShares = 9'999'999'999'999'985, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'981, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'979, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'982, .holderShares = 9'999'999'999'999'981, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'982, .expected = tecHAS_OBLIGATIONS},
            {.vault = {.available = 9'499'999'999'999'980, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'983, .holderShares = 9'999'999'999'999'982, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'982, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 9'499'999'999'999'981, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'984, .holderShares = 9'999'999'999'999'983, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'982, .expected = tecINSUFFICIENT_FUNDS},
            {.vault = {.available = 9'499'999'999'999'982, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'985, .holderShares = 9'999'999'999'999'984, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'982, .expected = tesSUCCESS},
            {.vault = {.available = 9'499'999'999'999'983, .deployed = 500'000'000'000'003, .sharesTotal = 9'999'999'999'999'986, .holderShares = 9'999'999'999'999'985, .earlyExitFeeRate = 5'000}, .subscription = -1'000, .redemption = 1'000'000, .amount = 9'999'999'999'999'982, .expected = tesSUCCESS},
        };
        // clang-format on

        std::uint32_t const p = parentCloseTime(env);
        auto const run = [&](std::string const& name,
                             TestVaults const& vaults,
                             std::span<DateCase const> cases) {
            for (auto const& [vault, holder] : vaults)
            {
                beginCase(("withdraw " + vaultName(env, vault) + " " + name).c_str());
                for (auto const& [row, subscription, redemption, amount, expected, byShares] :
                     cases)
                {
                    StagedVault staged = row;
                    staged.subscriptionDate = static_cast<std::uint32_t>(p + subscription);
                    staged.redemptionDate = static_cast<std::uint32_t>(p + redemption);
                    STAmount const withdrawal = byShares ? STAmount{shareIssue(env, vault), amount}
                                                         : vaultUnits(env, vault, amount);
                    StagedAmounts const amounts = stagedAmounts(env, vault, staged);
                    AppliedVaultTx const cpp =
                        applyWithdraw(env, vault, holder, amounts, withdrawal);
                    LeanVaultResult const lean =
                        leanWithdraw(cpp, amounts, withdrawal, byShares, p);
                    expectSame(*this, sampleText(staged, withdrawal), cpp, lean, expected);
                }
            }
        };

        run("subscription end", s.all, kSubscriptionEnd);
        run("redemption start", s.all, kRedemptionStart);
        run("fee phase", s.all, kFeePhase);
        run("full fee dust", s.ious, kFullFeeDust);
        run("fee consumes payout", s.all, kFeeConsumesPayout);
        run("net over available", s.all, kNetOverAvailable);
    }

    // Phase matrix: a withdrawal by assets of 400 from a 1000 IOU vault. Only the Investment
    // phase of a vault with an early-exit fee rate (even zero) charges the fee or, without the
    // field, rejects the withdrawal. Covered at the dates by testClosedEndedWithdrawBoundaries.
    void
    testClosedEndedWithdraw(
        jtx::Env& env,
        Setup const& s,
        VaultPhase phase,
        std::optional<std::uint32_t> earlyExitFeeRate,
        TER expected,
        std::optional<Number> const& expectedPayout = std::nullopt,
        bool onDate = false)
    {
        testcase("withdraw " + phaseName(phase, onDate) + ", " + feeName(earlyExitFeeRate));
        Keylet const& vault = s.iouDefaultScaleVault;
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), phase, earlyExitFeeRate, onDate);
        expectStagedWithdraw(
            env, vault, s.holder, staged, s.issuer["USD"](400), expected, expectedPayout);
    }

    // By shares: 400 of the 1000 shares (scale 6: 4e8) at a 5% fee pay 380.
    void
    testWithdrawBySharesInInvestment(jtx::Env& env, Setup const& s)
    {
        testcase("withdraw by shares in investment at a 5% fee");
        Keylet const& vault = s.iouDefaultScaleVault;
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee5Pct);
        expectStagedWithdraw(
            env,
            vault,
            s.holder,
            staged,
            STAmount{shareIssue(env, vault), 400'000'000},
            tesSUCCESS,
            Number{380});
    }

    // A final withdrawal (all outstanding shares) skips the fee even during Investment.
    void
    testWithdrawAllSharesInInvestment(jtx::Env& env, Setup const& s)
    {
        testcase("withdraw all shares in investment with a fee");
        Keylet const& vault = s.iouDefaultScaleVault;
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee5Pct);
        expectStagedWithdraw(
            env,
            vault,
            s.holder,
            staged,
            STAmount{shareIssue(env, vault), kInitialDepositUnits},
            tesSUCCESS,
            Number{1'000});
    }

    // Availability is checked against the gross amount without a fee and against the net payout
    // with one: 610 of the 1000 are deployed, so withdrawing 400 fails at a zero rate and pays 380
    // at 5%.
    void
    testWithdrawGrossOverAvailable(
        jtx::Env& env,
        Setup const& s,
        std::uint32_t earlyExitFeeRate,
        TER expected,
        Number const& available = Number{390})
    {
        testcase(
            "withdraw 400 with " + to_string(available) + " available at " +
            feeName(earlyExitFeeRate));
        Keylet const& vault = s.iouDefaultScaleVault;
        jtx::PrettyAsset const asset = s.issuer["USD"];
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        staged.available = asset(available);
        staged.deployed = asset(Number{1'000} - available);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, earlyExitFeeRate);
        expectStagedWithdraw(
            env,
            vault,
            s.holder,
            staged,
            asset(400),
            expected,
            expected == tesSUCCESS ? std::optional<Number>{Number{380}} : std::nullopt);
    }

    // A 16-digit amount at a 3.333% rate: the fee needs more digits than Number keeps, so the
    // upward fee and downward subtraction must round the same way on both sides.
    void
    testWithdrawInexactFee(jtx::Env& env, Setup const& s)
    {
        testcase("withdraw a 16-digit amount at an inexact fee rate");
        Keylet const& vault = s.iouDefaultScaleVault;
        // An initial deposit of 2e9 at scale 6.
        StagedAmounts staged = depositedVault(env, vault, 2'000'000'000'000'000);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, 3'333);
        expectStagedWithdraw(
            env,
            vault,
            s.holder,
            staged,
            jtx::PrettyAsset{s.issuer["USD"]}(Number{1'234'567'891'234'567LL, -6}),
            tesSUCCESS);
    }

    // XRP: a 50% fee on one drop leaves half a drop, which is zero in drops.
    void
    testWithdrawFeeConsumesPayout(jtx::Env& env, Setup const& s)
    {
        testcase("withdraw one drop in investment at a 50% fee");
        StagedAmounts staged = depositedVault(env, s.xrpVault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee50Pct);
        expectStagedWithdraw(
            env, s.xrpVault, s.depositor, staged, jtx::drops(1), tecPRECISION_LOSS);
    }

    // IOU: a 50% fee on one grid unit (1e-6) leaves 5e-7, representable but below the vault grid.
    void
    testWithdrawFeeLeavesSubGridPayout(jtx::Env& env, Setup const& s)
    {
        testcase("withdraw one grid unit in investment at a 50% fee");
        Keylet const& vault = s.iouDefaultScaleVault;
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, kFee50Pct);
        expectStagedWithdraw(
            env,
            vault,
            s.holder,
            staged,
            jtx::PrettyAsset{s.issuer["USD"]}(Number{1, -6}),
            tecPRECISION_LOSS);
    }

    void
    runTests() override
    {
        using namespace jtx;

        Env env{*this, vaultTestAmendments()};
        Setup const s = setup(env);
        Keylet const& iouVault = s.iouDefaultScaleVault;

        // Partial and final withdrawal by assets. IOU is scale 6, MPT is scale 0 (like XRP), so the
        // two cover the distinct share arithmetic
        testWithdrawIOU(env, iouVault, s.issuer, Number{1'000}, Number{400}, tesSUCCESS);
        testWithdrawIOU(env, iouVault, s.issuer, Number{1'000}, Number{1'000}, tesSUCCESS);
        testWithdrawMPT(env, s.mptVault, s.depositor, 1'000, 400, tesSUCCESS);
        testWithdrawMPT(env, s.mptVault, s.depositor, 1'000, 1'000, tesSUCCESS);
        testWithdrawXRP(env, s.xrpVault, s.depositor, XRP(1'000), drops(1), tesSUCCESS);

        // Insufficient vault assets (the check is asset-agnostic, so one case suffices).
        // covered by testWithdrawBoundaries
        testWithdrawIOU(
            env, iouVault, s.issuer, Number{1'000}, Number{1'001}, tecINSUFFICIENT_FUNDS);
        // Sub-share withdrawal: the amount converts to zero shares.
        // covered by testWithdrawBoundaries
        testWithdrawIOU(env, iouVault, s.issuer, Number{1, 9}, Number{1, -7}, tecPRECISION_LOSS);
        // MPT at the open limit.
        testWithdrawMPT(env, s.mptVault, s.depositor, kOpenLimitUnits, kOpenLimitUnits, tesSUCCESS);

        // covered by testWithdrawBoundaries
        testWithdrawAllShares(env, iouVault, s.issuer);

        // Direct sharesToAssetsWithdraw checks
        testSharesToAssets(env, iouVault, s.issuer, Number{1'000}, Number{0}, 1);
        testSharesToAssets(env, iouVault, s.issuer, Number{1'000}, Number{0}, 500'000'000);
        testSharesToAssets(env, iouVault, s.issuer, Number{1'000}, Number{0}, 999'999'999);
        testSharesToAssets(env, iouVault, s.issuer, Number{1'000}, Number{2'000}, 333'333'333);
        testSharesToAssets(env, iouVault, s.issuer, Number{1'000}, Number{500}, 123'456'789);
        testSharesToAssets(env, iouVault, s.issuer, Number{1'000'000}, Number{0}, 123'456'789);
        testSharesToAssets(env, iouVault, s.issuer, Number{1}, Number{1'000'000}, 500'000);

        // Staged extreme states (a 1000-asset seed mints 1e9 shares at scale 6). Each mixes an
        // extreme across a different field: AssetsTotal, AssetsAvailable, sharesTotal, shareAmount.
        Number const iouMax{9'999'999'999'999'999LL, 80};
        // Extreme AssetsTotal, tiny available, full shareholder
        testWithdrawUpdatedState(
            env,
            iouVault,
            s.issuer,
            iouMax,
            Number{1},
            1'000'000'000,
            500'000'000,
            tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, mid available, minimal sharesTotal/shareAmount: a full exit while
        // assets are deployed
        // covered by testWithdrawBoundaries
        testWithdrawUpdatedState(
            env, iouVault, s.issuer, iouMax, Number{1, 50}, 1, 1, tecHAS_OBLIGATIONS);
        // Most assets lent out: half the shares are worth more than is available
        // covered by testWithdrawBoundaries
        testWithdrawUpdatedState(
            env,
            iouVault,
            s.issuer,
            Number{1'000},
            Number{100},
            1'000'000'000,
            500'000'000,
            tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, tiny available, extreme sharesTotal, minimal shareAmount
        testWithdrawUpdatedState(
            env, iouVault, s.issuer, iouMax, Number{1}, 1'000'000'000, 1, tecINSUFFICIENT_FUNDS);
        // Overflow: NAV * shares / sharesTotal exceeds the IOU domain
        // covered by testWithdrawBoundaries
        testWithdrawUpdatedState(
            env, iouVault, s.issuer, iouMax, iouMax, 1'000, 1'000'000'000, tecPATH_DRY);
        // Overflow: minimal sharesTotal with a maximal shareAmount,
        // covered by testWithdrawBoundaries
        testWithdrawUpdatedState(
            env, iouVault, s.issuer, iouMax, Number{1}, 1, 1'000'000'000, tecPATH_DRY);
        // Overflow: sharesTotal * assets / NAV exceeds the MPT domain (by assets).
        // covered by testWithdrawBoundaries
        testWithdrawAssetsShareOverflow(env, iouVault, s.issuer, tecPATH_DRY);

        // Open discrepancy, disabled until the C++ code is fixed.
        // clang-format off
        // testWithdrawOvershoot();      // FV_M2_9: full withdrawal overshoots (both sides)

        // Properties both sides now satisfy, kept as regression tests.
        testWithdrawOvervaluedShares(env, s.xrpVault, s.depositor);  // FV_M2_3: a single-share payout rounds to nearest
        testWithdrawDilution();          // FV_M2_8: the share price does not fall
        testWithdrawDrainsVault(env, s.iouMinScaleVault, s.issuer);  // FV_M2_16: staged past the open limit, both sides agree
        testWithdrawAppliedDelta();      // totals move by exactly the payout

        // Fixed discrepancies, kept as regression tests.
        // FV_M2_15: a 6e-6 payout is below the 1e-5 ULP of a staged 1.2e10 total; the clamp floors
        // it to zero rather than moving the vault's books by a full ULP. Both sides reject.
        testWithdrawAssetsStaged(
            env,
            iouVault,
            s.issuer,
            Number{1'234'567'890'123'456LL, -5},
            12'345'678'901'234'560ULL,
            Number{6, -6},
            tecPRECISION_LOSS);
        // covered by testWithdrawBoundaries
        testWithdrawFinalWithLoss(env, iouVault, s.issuer, Number{100}, Number{10});  // FV_M2_13: full exit with a loss
        testWithdrawWaiveLoss();              // FV_M2_6: doApply now honors the waiver
        testWithdrawDustDebit(env, iouVault, s.issuer, Number{2, 12}, 1'000'000'000'000'000'000ULL);  // FV_M2_12 (2e12)
        testWithdrawDustDebit(env, iouVault, s.issuer, Number{15, 12}, 9'200'000'000'000'000'000ULL); // FV_M2_12 (1.5e13)
        // One share worth 0.3 units of an MPT pays nothing: rejected rather than burned.
        // covered by testWithdrawBoundaries
        testWithdrawUpdatedStateMPT(env, s.mptVault, s.depositor, Number{1'000}, 3'333, 1, tecPRECISION_LOSS);
        // covered by testWithdrawBoundaries
        testWithdrawFromFullyImpairedVault(env, iouVault, s.issuer);
        // covered by testWithdrawBoundaries
        testWithdrawMoreSharesThanHeld(env, iouVault, s.issuer);
        testWithdrawFromEmptyVault(false, tecPRECISION_LOSS);
        testWithdrawFromEmptyVault(true, tecINSUFFICIENT_FUNDS);
        // FV_M2_4: a 1e-6 withdrawal below the 1e-5 ULP of a staged ~1e10 total.
        testWithdrawPrecisionLossStaged(env, iouVault, s.issuer, Number{1'000'000'000'000'001LL, -5});
        testWithdrawPrecisionLossStaged(env, iouVault, s.issuer, Number{1'000'000'000'000'000LL, -5});
        // clang-format on

        testWithdrawBoundaries(env, s);

        // Without an early-exit fee field only Investment is closed.
        testClosedEndedWithdraw(env, s, VaultPhase::NoPhase, std::nullopt, tesSUCCESS, Number{400});
        testClosedEndedWithdraw(
            env, s, VaultPhase::Subscription, std::nullopt, tesSUCCESS, Number{400});
        testClosedEndedWithdraw(
            env, s, VaultPhase::Subscription, std::nullopt, tesSUCCESS, Number{400}, kOnDate);
        testClosedEndedWithdraw(env, s, VaultPhase::Investment, std::nullopt, tecTOO_SOON);
        testClosedEndedWithdraw(
            env, s, VaultPhase::Redemption, std::nullopt, tesSUCCESS, Number{400}, kOnDate);
        testClosedEndedWithdraw(
            env, s, VaultPhase::Redemption, std::nullopt, tesSUCCESS, Number{400});
        // A zero fee rate opens Investment without charging anything.
        testClosedEndedWithdraw(env, s, VaultPhase::Investment, 0, tesSUCCESS, Number{400});
        // A 5% fee applies in Investment only: 400 - 20 = 380.
        testClosedEndedWithdraw(
            env, s, VaultPhase::Subscription, kFee5Pct, tesSUCCESS, Number{400});
        testClosedEndedWithdraw(
            env, s, VaultPhase::Subscription, kFee5Pct, tesSUCCESS, Number{400}, kOnDate);
        testClosedEndedWithdraw(env, s, VaultPhase::Investment, kFee5Pct, tesSUCCESS, Number{380});
        testClosedEndedWithdraw(
            env, s, VaultPhase::Redemption, kFee5Pct, tesSUCCESS, Number{400}, kOnDate);
        testClosedEndedWithdraw(env, s, VaultPhase::Redemption, kFee5Pct, tesSUCCESS, Number{400});
        // A 100% fee burns the shares and pays nothing.
        testClosedEndedWithdraw(env, s, VaultPhase::Investment, kFee100Pct, tesSUCCESS, Number{0});

        testWithdrawBySharesInInvestment(env, s);
        testWithdrawAllSharesInInvestment(env, s);
        testWithdrawGrossOverAvailable(env, s, 0, tecINSUFFICIENT_FUNDS);
        testWithdrawGrossOverAvailable(env, s, kFee5Pct, tesSUCCESS);
        // The net payout (380) itself exceeds what is available.
        testWithdrawGrossOverAvailable(env, s, kFee5Pct, tecINSUFFICIENT_FUNDS, Number{300});
        testWithdrawInexactFee(env, s);
        testWithdrawFeeConsumesPayout(env, s);
        testWithdrawFeeLeavesSubGridPayout(env, s);

        testClosedEndedWithdrawBoundaries(env, s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultWithdraw, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
