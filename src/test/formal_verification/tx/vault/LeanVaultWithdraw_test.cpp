#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/formal_verification/tx/vault/WithdrawSweepCases.h>
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
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

using namespace withdraw_sweep;

class LeanVaultWithdraw_test : public LeanSuite
{
    static MPTIssue
    shareIssue(jtx::Env& env, Keylet const& vaultKeylet)
    {
        return MPTIssue{env.le(vaultKeylet)->at(sfShareMPTID)};
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
        Vault const state = readVaultState(env, vaultKeylet, asset);
        bool const byShares = amount.asset() != asset;
        bool const waiveUnrealizedLoss = holderOwnsAllShares(env, vaultKeylet, withdrawer);
        LeanVaultResult const withdraw = leanVaultWithdraw(
            state,
            amount,
            byShares,
            parentCloseTime(env),
            waiveUnrealizedLoss,
            Number{fetchHolderShares(env, vaultKeylet, withdrawer)});
        expectLawful(withdraw);

        env(jtx::Vault::withdraw(
                {.depositor = withdrawer, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        Vault const cpp = readVaultState(env, vaultKeylet, asset);
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!withdraw.leanError.has_value(), "lean withdraw error");

        TER const leanTer = withdraw.error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            leanTer == expected,
            std::string("lean=") + transToken(leanTer) + " expected " + transToken(expected));

        if (cppTer != tesSUCCESS)
            return;

        Number const& cppAssetsTotal = cpp.assetsTotal;
        Number const& cppAssetsAvailable = cpp.assetsAvailable;
        Number const& cppSharesTotal = cpp.sharesTotal;
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
        Number const& cppLossUnrealized = cpp.lossUnrealized;
        BEAST_EXPECTS(
            withdraw.vault.lossUnrealized == cppLossUnrealized,
            "lossUnrealized lean=" + to_string(withdraw.vault.lossUnrealized) +
                " cpp=" + to_string(cppLossUnrealized));
    }

    void
    expectStagedWithdraw(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        StagedVault const& staged,
        STAmount const& amount,
        TER expected)
    {
        TER const ter = checkWithdraw(*this, env, vault, holder, staged, amount).ter;
        BEAST_EXPECTS(
            ter == expected, "cpp=" + transToken(ter) + " expected " + transToken(expected));
    }

    // A vault after a first deposit of `seed` by the holder, who owns the seed * 10^scale shares.
    static StagedVault
    seededVault(jtx::Env& env, Keylet const& vault, STAmount const& seed)
    {
        int const scale = env.le(vault)->at(sfScale);
        auto const shares =
            static_cast<std::uint64_t>(static_cast<std::int64_t>(Number{seed} * Number{1, scale}));
        return StagedVault{.available = seed, .sharesTotal = shares, .holderShares = shares};
    }

    // A state staged over a vault the holder seeded with 1000 units (the holder keeps the seed's
    // shares); the total splits into `available` and the deployed rest.
    static StagedVault
    overSeed(
        jtx::Env& env,
        Keylet const& vault,
        Number const& assetsTotal,
        Number const& assetsAvailable,
        std::uint64_t sharesTotal)
    {
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedVault staged = seededVault(env, vault, STAmount{asset, Number{1'000}});
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
            seededVault(env, vault, gridUnits(env, vault, seed)),
            gridUnits(env, vault, amount),
            expected);
    }

    void
    testWithdrawAllShares(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("withdraw all shares (full redemption)");
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedVault const staged = seededVault(env, vault, STAmount{asset, Number{1'000}});
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
        StagedVault staged = seededVault(env, vault, STAmount{asset, seed});
        staged.available = STAmount{asset, seed + donation};
        STAmount const shares{shareIssue(env, vault), shareCount};
        AppliedVaultTx const cpp = checkWithdraw(*this, env, vault, holder, staged, shares);
        BEAST_EXPECTS(cpp.ter == tesSUCCESS, "cpp=" + transToken(cpp.ter));
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

        Env env(*this);
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
        StagedVault staged = seededVault(env, vault, STAmount{asset, Number{2'000}});
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
    void
    testWithdrawFromFullyImpairedVault(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder)
    {
        testcase("withdraw shares from a fully impaired vault with two holders");
        // The holder deposited 1000 and another holder 10, then the whole total was lost.
        Asset const asset = env.le(vault)->at(sfAsset);
        StagedVault staged = overSeed(env, vault, Number{1'010}, Number{0}, 0);
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

    // Finding (C++ bug): a share withdrawal pays round-to-nearest, so a single-share withdraw from
    // a vault pays more than the share is worth.
    void
    testWithdrawOvervaluedShares(jtx::Env& env, Keylet const& vault, jtx::Account const& holder)
    {
        testcase("withdraw overvalued shares");
        // bob deposits 3 drops (3 shares) and the owner donates 2 drops, so 3 shares now back
        // 5 drops (1 share = 1.667 drops). A single-share withdraw pays round(1.667) = 2 in C++,
        // 1 in model.
        StagedVault staged = seededVault(env, vault, gridUnits(env, vault, 3));
        staged.available = gridUnits(env, vault, 5);
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
        StagedVault staged = seededVault(env, vault, STAmount{asset, assetsTotal});
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
        StagedVault const staged = seededVault(env, vault, STAmount{asset, Number{1, 17}});
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

        Env env(*this);
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
        StagedVault staged = seededVault(env, vault, STAmount{asset, Number{1, 6}});
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

        Env env(*this);
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

    // ---- Sweeps --------------------------------------------------------------------------------

    // The vaults a sweep runs on, each with the account that withdraws from it.
    using SweepVaults = std::vector<std::pair<Keylet, jtx::Account>>;

    // A staged vault in its Investment phase (closed-ended, between its two dates) with an
    // early-exit fee rate.
    static StagedVault
    inInvestment(jtx::Env& env, StagedVault staged, std::int64_t rate)
    {
        std::uint32_t const now = parentCloseTime(env);
        staged.subscriptionDate = now - 1'000;
        staged.redemptionDate = now + 1'000'000;
        staged.earlyExitFeeRate = static_cast<std::uint32_t>(rate);
        return staged;
    }

    // A by-shares redemption row: `nav` available, nothing deployed, all shares held.
    TER
    checkRedeemCase(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        RedeemCusp const& c,
        std::optional<std::int64_t> feeRate = std::nullopt)
    {
        StagedVault staged{
            .available = gridUnits(env, vault, c.nav),
            .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal)};
        if (feeRate)
            staged = inInvestment(env, staged, *feeRate);
        return checkWithdraw(
                   *this, env, vault, holder, staged, STAmount{shareIssue(env, vault), c.shares})
            .ter;
    }

    // Zero shares by assets: an amount worth trunc(shares total * amount / assets total) = 0
    // shares is rejected (tecPRECISION_LOSS). Each row (the deposit zero-shares rows) burns
    // exactly one share.
    void
    testZeroSharesByAssetsSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(
                ("withdraw " + vaultName(env, vault) + " zero shares by assets-Sweep").c_str());
            runAroundCusp(kZeroSharesByAssetsCases, [&](PriceCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.total),
                    .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal)};
                return checkWithdraw(
                           *this, env, vault, holder, staged, gridUnits(env, vault, c.amount))
                    .ter;
            });
        }
    }

    // Zero payout: a by-shares redemption paying round(nav * shares / shares total) = 0 units is
    // rejected (tecPRECISION_LOSS). Each row pays exactly half a unit, which rounds to even (0).
    void
    testZeroPayoutSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " zero payout-Sweep").c_str());
            runAroundCusp(kZeroPayoutCases, [&](RedeemCusp const& c) {
                return checkRedeemCase(env, vault, holder, c);
            });
        }
    }

    // Clamp to zero: a by-shares payout below one grid step floors to zero and is rejected
    // (tecPRECISION_LOSS). Each row pays exactly one grid step.
    void
    testClampToZeroSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " clamp to zero-Sweep").c_str());
            runAroundCusp(kClampToZeroBySharesCases, [&](RedeemCusp const& c) {
                return checkRedeemCase(env, vault, holder, c);
            });
        }
    }

    // Payout out of range: a by-shares request for far more shares than exist converts to more
    // than the asset can represent and is rejected before the holder's shares are checked. Each
    // row pays exactly the largest amount (then fails on the holder's shares). XRP: C++
    // tefEXCEPTION (an uncaught runtime_error), the model outOfRange; both reject.
    void
    testPayoutRangeSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " payout range-Sweep").c_str());
            bool const native = Asset{env.le(vault)->at(sfAsset)}.native();
            runAroundCusp(
                native ? kXrpPayoutRangeCases : kMptPayoutRangeCases,
                [&](RedeemCusp const& c) { return checkRedeemCase(env, vault, holder, c); });
        }
    }

    // To-nearest switch: a payout of X + 1/2 units truncates below X = 10^15 and rounds to even
    // from there, where the payout amount itself rounds to the grid. Both sides succeed at every
    // row; the post-state and payout are compared.
    void
    testToNearestSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " to nearest-Sweep").c_str());
            runAroundCusp(
                kToNearestCases,
                [&](RedeemCusp const& c) { return checkRedeemCase(env, vault, holder, c); },
                false);
        }
    }

    // Dust with a 100% early-exit fee: a debit too small to change the stored available assets is
    // rejected (tecPRECISION_LOSS); with a 100% fee no clamp runs, so this check alone decides.
    // Each row debits exactly half the last stored digit.
    void
    testFullFeeDustSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " full fee dust-Sweep").c_str());
            runAroundCusp(kFullFeeDustCases, [&](RedeemCusp const& c) {
                return checkRedeemCase(env, vault, holder, c, kFeeRateMaximum);
            });
        }
    }

    // Available assets: with assets deployed, a withdrawal above the available assets is rejected
    // (tecINSUFFICIENT_FUNDS). Each row withdraws exactly the available assets, at price 1.
    void
    testAvailableSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " available-Sweep").c_str());
            runAroundCusp(kAvailableCases, [&](AvailableCusp const& c) {
                auto const sharesTotal = static_cast<std::uint64_t>(c.available + c.deployed);
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.available),
                    .deployed = gridUnits(env, vault, c.deployed),
                    .sharesTotal = sharesTotal,
                    .holderShares = sharesTotal - 1};
                return checkWithdraw(
                           *this, env, vault, holder, staged, gridUnits(env, vault, c.amount))
                    .ter;
            });
        }
    }

    // Fee consumes the payout: in Investment the payout gross - fee (fee rounded up, payout down)
    // must be at least one unit (tecPRECISION_LOSS below); a 100% rate pays nothing and succeeds.
    // Each row pays exactly one unit.
    void
    testFeeConsumesPayoutSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " fee consumes payout-Sweep").c_str());
            runAroundCusp(kFeeConsumesPayoutCases, [&](FeeCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, 1'000'000),
                    .sharesTotal = 1'000'000,
                    .holderShares = 999'999};
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           inInvestment(env, staged, c.rate),
                           gridUnits(env, vault, c.gross))
                    .ter;
            });
        }
    }

    // Net payout over available: with a fee only the net payout must be available
    // (tecINSUFFICIENT_FUNDS above). Each row nets exactly the available assets, at price 1.
    void
    testNetOverAvailableSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " net over available-Sweep").c_str());
            runAroundCusp(kNetOverAvailableCases, [&](NetOverAvailableCusp const& c) {
                auto const sharesTotal = static_cast<std::uint64_t>(c.available + c.deployed);
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.available),
                    .deployed = gridUnits(env, vault, c.deployed),
                    .sharesTotal = sharesTotal,
                    .holderShares = sharesTotal - 1};
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           inInvestment(env, staged, c.rate),
                           gridUnits(env, vault, c.gross))
                    .ter;
            });
        }
    }

    // Final withdrawal: redeeming every share pays all available assets, and is rejected while
    // assets are deployed (tecHAS_OBLIGATIONS). Each row redeems every share of a vault with
    // nothing deployed, at price 1.
    void
    testFinalSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " final-Sweep").c_str());
            runAroundCusp(kFinalCases, [&](FinalCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.available),
                    .deployed = gridUnits(env, vault, c.deployed),
                    .sharesTotal = static_cast<std::uint64_t>(c.available + c.deployed)};
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           staged,
                           STAmount{shareIssue(env, vault), c.shares})
                    .ter;
            });
        }
    }

    // Fully impaired vault: with a zero net asset value a by-shares redemption burns the shares
    // for nothing (tesSUCCESS); one unit of net asset value makes the payout non-zero, which fails
    // (tecPRECISION_LOSS or tecINSUFFICIENT_FUNDS). Each row has the whole deployed total lost.
    void
    testImpairedSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " fully impaired-Sweep").c_str());
            runAroundCusp(kImpairedCases, [&](ImpairedCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, 0),
                    .deployed = gridUnits(env, vault, c.deployed),
                    .loss = gridUnits(env, vault, c.loss),
                    .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
                    .holderShares = static_cast<std::uint64_t>(c.sharesTotal - 1)};
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           staged,
                           STAmount{shareIssue(env, vault), c.shares})
                    .ter;
            });
        }
    }

    // Sub-grid payout over available: a payout a tenth of a unit above the available assets is
    // rejected (tecINSUFFICIENT_FUNDS) by the check on the unclamped payout, which the clamp would
    // otherwise floor back to the available assets. Each row pays exactly the available assets.
    void
    testSubGridOverAvailableSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(
                ("withdraw " + vaultName(env, vault) + " sub-grid over available-Sweep").c_str());
            runAroundCusp(kSubGridOverAvailableCases, [&](SubGridCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.available),
                    .deployed = gridUnits(env, vault, c.deployed),
                    .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal),
                    .holderShares = static_cast<std::uint64_t>(c.sharesTotal - 1)};
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           staged,
                           STAmount{shareIssue(env, vault), c.shares})
                    .ter;
            });
        }
    }

    // Decade-crossing outflow: the payout is truncated to the grid of available - amount, ten
    // units from 10^16 units up, so there a one-unit withdrawal truncates to zero
    // (tecPRECISION_LOSS). Each row leaves exactly 10^16 - 1 or 10^16 units, at price 1.
    void
    testDecadeSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " decade crossing-Sweep").c_str());
            auto const sle = env.le(vault);
            Asset const asset = sle->at(sfAsset);
            int const scale = sle->at(sfScale);
            runAroundCusp(kDecadeCases, [&](DecadeCusp const& c) {
                auto const sharesTotal = static_cast<std::uint64_t>(c.availableMantissa * 10);
                StagedVault const staged{
                    .available =
                        STAmount{asset, static_cast<std::uint64_t>(c.availableMantissa), 1 - scale},
                    .sharesTotal = sharesTotal,
                    .holderShares = sharesTotal - 1};
                return checkWithdraw(
                           *this, env, vault, holder, staged, gridUnits(env, vault, c.amount))
                    .ter;
            });
        }
    }

    // Holder's shares: redeeming more shares than the holder owns is rejected
    // (tecINSUFFICIENT_FUNDS). Each row redeems exactly the shares held; one more share is held by
    // someone else.
    void
    testHolderSharesSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " holder shares-Sweep").c_str());
            runAroundCusp(kHolderSharesCases, [&](HolderCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.holderShares + 1),
                    .sharesTotal = static_cast<std::uint64_t>(c.holderShares + 1),
                    .holderShares = static_cast<std::uint64_t>(c.holderShares)};
                return checkWithdraw(
                           *this,
                           env,
                           vault,
                           holder,
                           staged,
                           STAmount{shareIssue(env, vault), c.shares})
                    .ter;
            });
        }
    }

    // Sole-holder loss waiver: a holder of every share redeems at the assets total, any other at
    // assets total - loss unrealized. Both sides succeed; the post-state and payout are compared
    // for a 1000-share redemption.
    void
    testWaiverSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " loss waiver-Sweep").c_str());
            runAroundCusp(
                kWaiverCases,
                [&](WaiverCusp const& c) {
                    StagedVault const staged{
                        .available = gridUnits(env, vault, c.total - c.deployed),
                        .deployed = gridUnits(env, vault, c.deployed),
                        .loss = gridUnits(env, vault, c.loss),
                        .sharesTotal = static_cast<std::uint64_t>(c.total),
                        .holderShares = static_cast<std::uint64_t>(c.holderShares)};
                    return checkWithdraw(
                               *this,
                               env,
                               vault,
                               holder,
                               staged,
                               STAmount{shareIssue(env, vault), 1'000})
                        .ter;
                },
                false);
        }
    }

    // By-assets share overflow: an amount worth more than 2^63 - 1 shares fails the share
    // computation (tecPATH_DRY). Each row converts to exactly 2^63 - 1 shares.
    void
    testShareOverflowSweep(jtx::Env& env, SweepVaults const& vaults)
    {
        for (auto const& [vault, holder] : vaults)
        {
            beginCase(("withdraw " + vaultName(env, vault) + " share overflow-Sweep").c_str());
            runAroundCusp(kAssetsShareOverflowCases, [&](ShareOverflowCusp const& c) {
                StagedVault const staged{
                    .available = gridUnits(env, vault, c.nav),
                    .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal)};
                return checkWithdraw(
                           *this, env, vault, holder, staged, gridUnits(env, vault, c.amount))
                    .ter;
            });
        }
    }

    void
    runTests() override
    {
        using namespace jtx;

        // One ledger holding a vault per asset; every staged withdrawal (old tests and sweeps)
        // runs on a throwaway view of it.
        Env env{*this};
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const depositor{"depositor"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.fund(XRP(9'500'000'000), depositor);
        env.close();

        PrettyAsset const xrp = xrpIssue();
        PrettyAsset const iou = issuer["USD"];
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer, depositor, mpt(9'200'000'000'000'000)));
        env.close();

        // The IOU withdrawer is the issuer, which skips the C++-only trust-line checks.
        Keylet const xrpVault = createSweepVault(env, owner, depositor, xrp);
        Keylet const mptVault = createSweepVault(env, owner, depositor, mpt);
        // IOU at the smallest, the default and the largest vault scale.
        Keylet const iouScale0Vault = createSweepVault(env, owner, issuer, iou, 0);
        Keylet const iouScale6Vault = createSweepVault(env, owner, issuer, iou, 6);
        Keylet const iouScale10Vault = createSweepVault(env, owner, issuer, iou, 10);
        // Staged Investment dates sit 1000 s before the parent close time, which starts near 0.
        env.close(env.now() + std::chrono::seconds{100'000'000});

        // Partial and final withdrawal by assets. IOU is scale 6, MPT is scale 0 (like XRP), so the
        // two cover the distinct share arithmetic
        testWithdrawIOU(env, iouScale6Vault, issuer, Number{1'000}, Number{400}, tesSUCCESS);
        testWithdrawIOU(env, iouScale6Vault, issuer, Number{1'000}, Number{1'000}, tesSUCCESS);
        testWithdrawMPT(env, mptVault, depositor, 1'000, 400, tesSUCCESS);
        testWithdrawMPT(env, mptVault, depositor, 1'000, 1'000, tesSUCCESS);
        testWithdrawXRP(env, xrpVault, depositor, XRP(1'000), drops(1), tesSUCCESS);

        // Insufficient vault assets (the check is asset-agnostic, so one case suffices).
        // covered by testAvailableSweep
        testWithdrawIOU(
            env, iouScale6Vault, issuer, Number{1'000}, Number{1'001}, tecINSUFFICIENT_FUNDS);
        // Sub-share withdrawal: the amount converts to zero shares.
        // covered by testZeroSharesByAssetsSweep
        testWithdrawIOU(
            env, iouScale6Vault, issuer, Number{1, 9}, Number{1, -7}, tecPRECISION_LOSS);
        // MPT at the open limit.
        testWithdrawMPT(env, mptVault, depositor, kOpenLimitUnits, kOpenLimitUnits, tesSUCCESS);

        // covered by testFinalSweep
        testWithdrawAllShares(env, iouScale6Vault, issuer);

        // Direct sharesToAssetsWithdraw checks
        testSharesToAssets(env, iouScale6Vault, issuer, Number{1'000}, Number{0}, 1);
        testSharesToAssets(env, iouScale6Vault, issuer, Number{1'000}, Number{0}, 500'000'000);
        testSharesToAssets(env, iouScale6Vault, issuer, Number{1'000}, Number{0}, 999'999'999);
        testSharesToAssets(env, iouScale6Vault, issuer, Number{1'000}, Number{2'000}, 333'333'333);
        testSharesToAssets(env, iouScale6Vault, issuer, Number{1'000}, Number{500}, 123'456'789);
        testSharesToAssets(env, iouScale6Vault, issuer, Number{1'000'000}, Number{0}, 123'456'789);
        testSharesToAssets(env, iouScale6Vault, issuer, Number{1}, Number{1'000'000}, 500'000);

        // Staged extreme states (a 1000-asset seed mints 1e9 shares at scale 6). Each mixes an
        // extreme across a different field: AssetsTotal, AssetsAvailable, sharesTotal, shareAmount.
        Number const iouMax{9'999'999'999'999'999LL, 80};
        // Extreme AssetsTotal, tiny available, full shareholder
        testWithdrawUpdatedState(
            env,
            iouScale6Vault,
            issuer,
            iouMax,
            Number{1},
            1'000'000'000,
            500'000'000,
            tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, mid available, minimal sharesTotal/shareAmount: a full exit while
        // assets are deployed
        // covered by testFinalSweep
        testWithdrawUpdatedState(
            env, iouScale6Vault, issuer, iouMax, Number{1, 50}, 1, 1, tecHAS_OBLIGATIONS);
        // Most assets lent out: half the shares are worth more than is available
        // covered by testAvailableSweep
        testWithdrawUpdatedState(
            env,
            iouScale6Vault,
            issuer,
            Number{1'000},
            Number{100},
            1'000'000'000,
            500'000'000,
            tecINSUFFICIENT_FUNDS);
        // Extreme AssetsTotal, tiny available, extreme sharesTotal, minimal shareAmount
        testWithdrawUpdatedState(
            env,
            iouScale6Vault,
            issuer,
            iouMax,
            Number{1},
            1'000'000'000,
            1,
            tecINSUFFICIENT_FUNDS);
        // Overflow: NAV * shares / sharesTotal exceeds the IOU domain
        testWithdrawUpdatedState(
            env, iouScale6Vault, issuer, iouMax, iouMax, 1'000, 1'000'000'000, tecPATH_DRY);
        // Overflow: minimal sharesTotal with a maximal shareAmount,
        testWithdrawUpdatedState(
            env, iouScale6Vault, issuer, iouMax, Number{1}, 1, 1'000'000'000, tecPATH_DRY);
        // Overflow: sharesTotal * assets / NAV exceeds the MPT domain (by assets).
        // covered by testShareOverflowSweep
        testWithdrawAssetsShareOverflow(env, iouScale6Vault, issuer, tecPATH_DRY);

        // Open discrepancy, disabled until the C++ code is fixed.
        // clang-format off
        // testWithdrawOvershoot();      // FV_M2_9: full withdrawal overshoots (both sides)

        // Properties both sides now satisfy, kept as regression tests.
        testWithdrawOvervaluedShares(env, xrpVault, depositor);  // FV_M2_3: a single-share payout rounds down
        testWithdrawDilution();          // FV_M2_8: the share price does not fall
        testWithdrawDrainsVault(env, iouScale0Vault, issuer);  // FV_M2_16: staged past the open limit, both sides agree
        testWithdrawAppliedDelta();      // totals move by exactly the payout

        // Fixed discrepancies, kept as regression tests.
        // FV_M2_15: a 6e-6 payout is below the 1e-5 ULP of a staged 1.2e10 total; the clamp floors
        // it to zero rather than moving the vault's books by a full ULP. Both sides reject.
        testWithdrawAssetsStaged(
            env,
            iouScale6Vault,
            issuer,
            Number{1'234'567'890'123'456LL, -5},
            12'345'678'901'234'560ULL,
            Number{6, -6},
            tecPRECISION_LOSS);
        // covered by testFinalSweep
        testWithdrawFinalWithLoss(env, iouScale6Vault, issuer, Number{100}, Number{10});  // FV_M2_13: full exit with a loss
        testWithdrawWaiveLoss();              // FV_M2_6: doApply now honors the waiver
        testWithdrawDustDebit(env, iouScale6Vault, issuer, Number{2, 12}, 1'000'000'000'000'000'000ULL);  // FV_M2_12 (2e12)
        testWithdrawDustDebit(env, iouScale6Vault, issuer, Number{15, 12}, 9'200'000'000'000'000'000ULL); // FV_M2_12 (1.5e13)
        // One share worth 0.3 units of an MPT pays nothing: rejected rather than burned.
        // covered by testZeroPayoutSweep
        testWithdrawUpdatedStateMPT(env, mptVault, depositor, Number{1'000}, 3'333, 1, tecPRECISION_LOSS);
        // covered by testImpairedSweep
        testWithdrawFromFullyImpairedVault(env, iouScale6Vault, issuer);
        // covered by testHolderSharesSweep
        testWithdrawMoreSharesThanHeld(env, iouScale6Vault, issuer);
        testWithdrawFromEmptyVault(false, tecPRECISION_LOSS);
        testWithdrawFromEmptyVault(true, tecINSUFFICIENT_FUNDS);
        // FV_M2_4: a 1e-6 withdrawal below the 1e-5 ULP of a staged ~1e10 total.
        testWithdrawPrecisionLossStaged(env, iouScale6Vault, issuer, Number{1'000'000'000'000'001LL, -5});
        testWithdrawPrecisionLossStaged(env, iouScale6Vault, issuer, Number{1'000'000'000'000'000LL, -5});
        // clang-format on

        // Sweeps.
        SweepVaults const ious{
            {iouScale0Vault, issuer}, {iouScale6Vault, issuer}, {iouScale10Vault, issuer}};
        SweepVaults const integral{{xrpVault, depositor}, {mptVault, depositor}};
        SweepVaults all = integral;
        all.insert(all.end(), ious.begin(), ious.end());

        testZeroSharesByAssetsSweep(env, all);
        testZeroPayoutSweep(env, integral);
        testClampToZeroSweep(env, ious);
        testPayoutRangeSweep(env, integral);
        testToNearestSweep(env, ious);
        testFullFeeDustSweep(env, ious);
        testAvailableSweep(env, all);
        testFeeConsumesPayoutSweep(env, all);
        testNetOverAvailableSweep(env, all);
        testFinalSweep(env, all);
        testImpairedSweep(env, all);
        testSubGridOverAvailableSweep(env, ious);
        testDecadeSweep(env, ious);
        testHolderSharesSweep(env, all);
        testWaiverSweep(env, all);
        testShareOverflowSweep(env, integral);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultWithdraw, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
