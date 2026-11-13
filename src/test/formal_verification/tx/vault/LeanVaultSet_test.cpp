#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultSetFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <chrono>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

// The VaultSet AssetsMaximum is assetsMaximum * 10^exponent vault units (10^-scale for an IOU).
struct SetCase
{
    StagedVault vault;
    std::int64_t assetsMaximum;
    TER expected;
    int exponent{};
};

class LeanVaultSet_test : public LeanSuite
{
    // Every staged VaultSet runs on a throwaway view of one shared ledger and expects its verdict
    // on both sides, with every vault field equal when both succeed.
    // Staged states may be unreachable by any transaction: a verdict compares model and C++ on the
    // same pre-state and does not claim the state is reachable (see stageVault).

    // The model's VaultSet: canVaultUpdate, then update.
    static LeanVaultResult
    leanSet(
        Vault const& pre,
        std::optional<Number> const& cap,
        bool block = false,
        bool unblock = false)
    {
        LawfulTerResult const can = leanCanVaultUpdate(pre, cap, block, unblock);
        if (can.leanError)
            return {.leanError = can.leanError};
        if (can.ter != tesSUCCESS)
            return {.error = can.ter};
        LeanUpdateResult const updated = leanVaultUpdate(pre, cap, block, unblock);
        if (updated.leanError)
            return {.leanError = updated.leanError};
        return {.vault = updated.vault};
    }

    // VaultSet of `cap` on `staged`, and the model on the same pre-state. A zero cap is stored as
    // no cap on both sides.
    void
    expectSet(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& owner,
        StagedAmounts const& staged,
        Number const& cap,
        std::string const& at,
        TER expected)
    {
        auto tx = jtx::Vault::set({.owner = owner, .id = vault.key});
        tx[sfAssetsMaximum] = cap;
        AppliedVaultTx const cpp = applyStaged(env, vault, owner, staged, tx);
        expectSame(
            *this, at + "maximum " + to_string(cap) + ": ", cpp, leanSet(cpp.pre, cap), expected);
    }

    void
    runVaultSet(
        jtx::Env& env,
        Keylet const& xrpVault,
        jtx::Account const& owner,
        std::int64_t assetsTotal,
        std::int64_t assetsMaximum,
        TER expected)
    {
        testcase(
            "set max=" + std::to_string(assetsMaximum) + " total=" + std::to_string(assetsTotal));
        StagedVault const staged{
            .available = assetsTotal,
            .sharesTotal = static_cast<std::uint64_t>(assetsTotal),
        };
        expectSet(
            env,
            xrpVault,
            owner,
            stagedAmounts(env, xrpVault, staged),
            Number{assetsMaximum},
            sampleText(staged),
            expected);
    }

    // Deposit blocking: only a vault created with tfVaultOwnerCanBlockDeposit accepts the flags.
    void
    runBlockDeposit(bool ownerCanBlock, bool block, TER expected)
    {
        using namespace jtx;
        testcase(
            std::string(block ? "block" : "unblock") + " deposits, owner " +
            (ownerCanBlock ? "can" : "cannot") + " block");

        Env env{*this, vaultTestAmendments()};
        Account const owner{"owner"};
        env.fund(XRP(1'000'000), owner);
        env.close();

        jtx::Vault vault{env};
        auto const [createTx, vaultKeylet] = vault.create(
            {.owner = owner,
             .asset = xrpIssue(),
             .flags = ownerCanBlock ? std::optional<std::uint32_t>{tfVaultOwnerCanBlockDeposit}
                                    : std::nullopt});
        env(createTx);
        env.close();
        if (!block && ownerCanBlock)
        {
            // Block first, so the unblock changes the vault.
            env(jtx::Vault::set(
                    {.owner = owner, .id = vaultKeylet.key, .flags = tfVaultDepositBlock}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }

        Vault const state = readVaultState(env, vaultKeylet, xrpIssue());
        auto const lean = leanCanVaultUpdate(state, std::nullopt, block, !block);
        expectLawful(lean);

        env(jtx::Vault::set(
                {.owner = owner,
                 .id = vaultKeylet.key,
                 .flags = block ? tfVaultDepositBlock : tfVaultDepositUnblock}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Vault const cpp = readVaultState(env, vaultKeylet, xrpIssue());
        env.close();

        expectSame(
            *this,
            "",
            {.pre = state, .ter = cppTer, .post = cpp},
            leanSet(state, std::nullopt, block, !block),
            expected);
        if (cppTer == tesSUCCESS)
            BEAST_EXPECTS(cpp.depositBlocked == block, "depositBlocked not set as requested");
    }

    // Both deposit flags fail C++ preflight; the model's single optional flag cannot express them.
    void
    testBothDepositFlags(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        testcase("block and unblock deposits together");
        Vault const state = readVaultState(env, vault, xrpIssue());
        env(jtx::Vault::set(
                {.owner = owner,
                 .id = vault.key,
                 .flags = tfVaultDepositBlock | tfVaultDepositUnblock}),
            jtx::Ter(std::ignore));
        expectSame(
            *this,
            "",
            {.pre = state, .ter = env.ter(), .post = state},
            leanSet(state, std::nullopt, true, true),
            temINVALID_FLAG,
            LeanError::badInput);
    }

    // An IOU cap below the vault grid is rejected on both sides.
    void
    testCapOffGrid(jtx::Env& env, Keylet const& iouVault, jtx::Account const& owner)
    {
        testcase("set an IOU cap off the vault grid");
        expectSet(
            env,
            iouVault,
            owner,
            {.available = vaultUnits(env, iouVault, 0)},
            Number{1, -7},
            "",
            tecPRECISION_LOSS);
    }

    // VaultSet has no phase logic: the owner caps a closed-ended vault during Investment.
    void
    testSetInInvestment(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& owner,
        jtx::Account const& holder)
    {
        testcase("set assets maximum in investment");
        StagedAmounts staged = depositedVault(env, vault, kInitialDepositUnits);
        stagePhase(staged, parentCloseTime(env), VaultPhase::Investment, 5'000);
        Number const cap{5'000};
        auto tx = jtx::Vault::set({.owner = owner, .id = vault.key});
        tx[sfAssetsMaximum] = cap;
        AppliedVaultTx const cpp = applyStaged(env, vault, holder, staged, tx);
        auto const lean = leanCanVaultUpdate(cpp.pre, cap);
        expectLawful(lean);
        expectSame(*this, "investment: ", cpp, leanSet(cpp.pre, cap), tesSUCCESS);
        BEAST_EXPECTS(
            cpp.post.assetsMaximum == cap,
            "stored cap " + (cpp.post.assetsMaximum ? to_string(*cpp.post.assetsMaximum) : "none"));
    }

    // Finding (FV_M2_19, c++): VaultSet rounds an AssetsMaximum over 16 digits to the STAmount
    // grid via associateAsset, so the stored cap differs from the submitted value.
    void
    testAssetsMaximumRoundedToGrid()
    {
        using namespace jtx;
        testcase("AssetsMaximum over 16 digits is rounded on VaultSet");

        Env env{*this, vaultTestAmendments()};
        Account const owner{"owner"}, issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        PrettyAsset const asset = issuer["USD"];
        env.trust(asset(1'000), owner);
        env(pay(issuer, owner, asset(200)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());

        Number const submitted{12'345'678'901'234'567LL, -1};  // 17 significant digits
        auto tx = jtx::Vault::set({.owner = owner, .id = vaultKeylet.key});
        tx[sfAssetsMaximum] = submitted;
        env(tx);
        env.close();

        Number const stored = env.le(vaultKeylet)->at(sfAssetsMaximum);
        BEAST_EXPECTS(
            stored == submitted,
            "AssetsMaximum rounded to grid: submitted=" + to_string(submitted) +
                " stored=" + to_string(stored));
    }

    using TestVaults = std::vector<Keylet>;

    struct Setup
    {
        jtx::Account owner;
        // Holds a share of the default-scale IOU vault, which the investment test stages.
        jtx::Account holder;
        Keylet xrpVault;
        Keylet iouDefaultScaleVault;
        TestVaults xrp;
        TestVaults mpt;
        TestVaults iouMinScale;
        TestVaults iouDefaultScale;
        TestVaults iouMaxScale;
        TestVaults ious;
        TestVaults all;
    };

    static Setup
    setup(jtx::Env& env)
    {
        using namespace jtx;
        using namespace std::chrono_literals;
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();
        // Staged dates reach before the parent close time, which starts near 0.
        env.close(env.now() + 1'000'000'000s);
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        env.close();
        PrettyAsset const iou = issuer["USD"];
        env(trust(holder, iou(Number{1, 10})));
        env.close();
        env(pay(issuer, holder, iou(1)));
        env.close();
        Keylet const xrpVault = createVault(env, owner, xrpIssue());
        Keylet const mptVault = createVault(env, owner, mptt.issuanceID());
        Keylet const iouMinScaleVault = createVault(env, owner, iou, kVaultMinimumIouScale);
        Keylet const iouDefaultScaleVault = createVault(env, owner, iou, kVaultDefaultIouScale);
        Keylet const iouMaxScaleVault =
            createVault(env, owner, iou, kFixedPrecisionVaultMaximumIouScale);
        // The holder's share MPToken and the pseudo-account trust line, which staging needs.
        env(jtx::Vault::deposit({
            .depositor = holder,
            .id = iouDefaultScaleVault.key,
            .amount = vaultUnits(env, iouDefaultScaleVault, 1),
        }));
        env.close();
        return {
            .owner = owner,
            .holder = holder,
            .xrpVault = xrpVault,
            .iouDefaultScaleVault = iouDefaultScaleVault,
            .xrp = {xrpVault},
            .mpt = {mptVault},
            .iouMinScale = {iouMinScaleVault},
            .iouDefaultScale = {iouDefaultScaleVault},
            .iouMaxScale = {iouMaxScaleVault},
            .ious = {iouMinScaleVault, iouDefaultScaleVault, iouMaxScaleVault},
            .all = {xrpVault, mptVault, iouMinScaleVault, iouDefaultScaleVault, iouMaxScaleVault},
        };
    }

    // Each case stages its vault, sets its AssetsMaximum and expects its verdict on both sides.
    // - Maximum below total: a non-zero maximum below the assets total (available + deployed) is
    //   tecLIMIT_EXCEEDED; equal to it is accepted and 0 removes the cap. Each cusp sets the
    //   maximum to the total, split between available and deployed assets.
    // - Maximum below total, per asset: the same at the largest total the asset holds (XRP 1e17
    //   drops, MPT 2^63 - 1, 16 IOU digits); totals past it are not staged.
    // - Maximum grid: an IOU maximum off the vault grid 10^-scale, or with more than 16 digits, is
    //   tecPRECISION_LOSS. Each cusp is on the grid of an empty vault; moving the mantissa leaves
    //   it, except where the move only drops a digit.
    // - Maximum range: a maximum the asset cannot represent (XRP above 1e17 drops, MPT above
    //   2^63 - 1, IOU past 9999999999999999e80) is tecPRECISION_LOSS. Each cusp is the largest
    //   representable value; the IOU rows are per scale, as their exponent is in vault units.
    // clang-format off
    static constexpr SetCase kMaximumBelowTotal[] = {
        // available 2, deployed 0, maximum 2
        {.vault = {}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.available = 4, .sharesTotal = 4}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {}, .assetsMaximum = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .assetsMaximum = 1, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .assetsMaximum = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .sharesTotal = 3}, .assetsMaximum = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4, .sharesTotal = 4}, .assetsMaximum = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {}, .assetsMaximum = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .assetsMaximum = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .assetsMaximum = 2, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .assetsMaximum = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4, .sharesTotal = 4}, .assetsMaximum = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {}, .assetsMaximum = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .assetsMaximum = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .assetsMaximum = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .assetsMaximum = 3, .expected = tesSUCCESS},
        {.vault = {.available = 4, .sharesTotal = 4}, .assetsMaximum = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {}, .assetsMaximum = 4, .expected = tesSUCCESS},
        {.vault = {.available = 1, .sharesTotal = 1}, .assetsMaximum = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .sharesTotal = 2}, .assetsMaximum = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .sharesTotal = 3}, .assetsMaximum = 4, .expected = tesSUCCESS},
        {.vault = {.available = 4, .sharesTotal = 4}, .assetsMaximum = 4, .expected = tesSUCCESS},
        // available 1, deployed 1, maximum 2
        {.vault = {.deployed = 1, .sharesTotal = 1}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .assetsMaximum = 0, .expected = tesSUCCESS},
        {.vault = {.deployed = 1, .sharesTotal = 1}, .assetsMaximum = 1, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .assetsMaximum = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .assetsMaximum = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .assetsMaximum = 1, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 1, .sharesTotal = 1}, .assetsMaximum = 2, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .assetsMaximum = 2, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .assetsMaximum = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .assetsMaximum = 2, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 1, .sharesTotal = 1}, .assetsMaximum = 3, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .assetsMaximum = 3, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .assetsMaximum = 3, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .assetsMaximum = 3, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 1, .sharesTotal = 1}, .assetsMaximum = 4, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 1, .sharesTotal = 2}, .assetsMaximum = 4, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 1, .sharesTotal = 3}, .assetsMaximum = 4, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 1, .sharesTotal = 4}, .assetsMaximum = 4, .expected = tesSUCCESS},
        // available 1'000'000'000, deployed 0, maximum 1'000'000'000
        {.vault = {.available = 999'999'998, .sharesTotal = 999'999'998}, .assetsMaximum = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'998, .sharesTotal = 999'999'998}, .assetsMaximum = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'998, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'998, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'998, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'002, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        // available 1, deployed 999'999'999, maximum 1'000'000'000
        {.vault = {.deployed = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .deployed = 999'999'999, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .deployed = 999'999'999, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .deployed = 999'999'999, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 999'999'999, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 2, .deployed = 999'999'999, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .deployed = 999'999'999, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 999'999'999, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 999'999'999, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 3, .deployed = 999'999'999, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 999'999'999, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 999'999'999, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 999'999'999, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 999'999'999, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 999'999'999, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 2, .deployed = 999'999'999, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 3, .deployed = 999'999'999, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        // available 999'999'999, deployed 1, maximum 1'000'000'000
        {.vault = {.available = 999'999'997, .deployed = 1, .sharesTotal = 999'999'998}, .assetsMaximum = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'997, .deployed = 1, .sharesTotal = 999'999'998}, .assetsMaximum = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'997, .deployed = 1, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'997, .deployed = 1, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 999'999'997, .deployed = 1, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'998, .deployed = 1, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 999'999'999, .deployed = 1, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'000, .deployed = 1, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 1'000'000'001, .deployed = 1, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        // available 500'000'000, deployed 500'000'000, maximum 1'000'000'000
        {.vault = {.available = 499'999'998, .deployed = 500'000'000, .sharesTotal = 999'999'998}, .assetsMaximum = 999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .deployed = 500'000'000, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'001, .deployed = 500'000'000, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'002, .deployed = 500'000'000, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 499'999'998, .deployed = 500'000'000, .sharesTotal = 999'999'998}, .assetsMaximum = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .deployed = 500'000'000, .sharesTotal = 999'999'999}, .assetsMaximum = 999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'001, .deployed = 500'000'000, .sharesTotal = 1'000'000'001}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'002, .deployed = 500'000'000, .sharesTotal = 1'000'000'002}, .assetsMaximum = 999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 499'999'998, .deployed = 500'000'000, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .deployed = 500'000'000, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'001, .deployed = 500'000'000, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 500'000'002, .deployed = 500'000'000, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'000, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 499'999'998, .deployed = 500'000'000, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .deployed = 500'000'000, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'001, .deployed = 500'000'000, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'001, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'002, .deployed = 500'000'000, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'001, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 499'999'998, .deployed = 500'000'000, .sharesTotal = 999'999'998}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 499'999'999, .deployed = 500'000'000, .sharesTotal = 999'999'999}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'000, .deployed = 500'000'000, .sharesTotal = 1'000'000'000}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'001, .deployed = 500'000'000, .sharesTotal = 1'000'000'001}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
        {.vault = {.available = 500'000'002, .deployed = 500'000'000, .sharesTotal = 1'000'000'002}, .assetsMaximum = 1'000'000'002, .expected = tesSUCCESS},
    };
    static constexpr SetCase kMaximumBelowTotalXrp[] = {
        // available 100'000'000'000'000'000, deployed 0, maximum 100'000'000'000'000'000
        {.vault = {.available = 99'999'999'999'999'998, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 99'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'999, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 99'999'999'999'999'998, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'999, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 99'999'999'999'999'998, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'999, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 100'000'000'000'000'000, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        // available 1, deployed 99'999'999'999'999'999, maximum 100'000'000'000'000'000
        {.vault = {.deployed = 99'999'999'999'999'999, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .deployed = 99'999'999'999'999'999, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 99'999'999'999'999'999, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 99'999'999'999'999'999, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 99'999'999'999'999'999, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 99'999'999'999'999'999, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        // available 99'999'999'999'999'999, deployed 1, maximum 100'000'000'000'000'000
        {.vault = {.available = 99'999'999'999'999'997, .deployed = 1, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 99'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'998, .deployed = 1, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 99'999'999'999'999'999, .deployed = 1, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 99'999'999'999'999'997, .deployed = 1, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'998, .deployed = 1, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'999, .deployed = 1, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 99'999'999'999'999'997, .deployed = 1, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'998, .deployed = 1, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 99'999'999'999'999'999, .deployed = 1, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        // available 50'000'000'000'000'000, deployed 50'000'000'000'000'000, maximum 100'000'000'000'000'000
        {.vault = {.available = 49'999'999'999'999'998, .deployed = 50'000'000'000'000'000, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 99'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 49'999'999'999'999'999, .deployed = 50'000'000'000'000'000, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 50'000'000'000'000'000, .deployed = 50'000'000'000'000'000, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 49'999'999'999'999'998, .deployed = 50'000'000'000'000'000, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 49'999'999'999'999'999, .deployed = 50'000'000'000'000'000, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 50'000'000'000'000'000, .deployed = 50'000'000'000'000'000, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 99'999'999'999'999'999, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 49'999'999'999'999'998, .deployed = 50'000'000'000'000'000, .sharesTotal = 99'999'999'999'999'998}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 49'999'999'999'999'999, .deployed = 50'000'000'000'000'000, .sharesTotal = 99'999'999'999'999'999}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {.available = 50'000'000'000'000'000, .deployed = 50'000'000'000'000'000, .sharesTotal = 100'000'000'000'000'000}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
    };
    static constexpr SetCase kMaximumBelowTotalMpt[] = {
        // available 9'223'372'036'854'775'807, deployed 0, maximum 9'223'372'036'854'775'807
        {.vault = {.available = 9'223'372'036'854'775'805, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'223'372'036'854'775'807, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'223'372'036'854'775'805, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'807, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'223'372'036'854'775'805, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'807, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        // available 1, deployed 9'223'372'036'854'775'806, maximum 9'223'372'036'854'775'807
        {.vault = {.deployed = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .deployed = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'223'372'036'854'775'806, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        // available 9'223'372'036'854'775'806, deployed 1, maximum 9'223'372'036'854'775'807
        {.vault = {.available = 9'223'372'036'854'775'804, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'805, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'223'372'036'854'775'806, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'223'372'036'854'775'804, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'805, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'806, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'223'372'036'854'775'804, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'805, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        {.vault = {.available = 9'223'372'036'854'775'806, .deployed = 1, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        // available 4'611'686'018'427'387'903, deployed 4'611'686'018'427'387'904, maximum 9'223'372'036'854'775'807
        {.vault = {.available = 4'611'686'018'427'387'901, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tesSUCCESS},
        {.vault = {.available = 4'611'686'018'427'387'902, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'611'686'018'427'387'903, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'805, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'611'686'018'427'387'901, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tesSUCCESS},
        {.vault = {.available = 4'611'686'018'427'387'902, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tesSUCCESS},
        {.vault = {.available = 4'611'686'018'427'387'903, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'806, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'611'686'018'427'387'901, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'805}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        {.vault = {.available = 4'611'686'018'427'387'902, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'806}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
        {.vault = {.available = 4'611'686'018'427'387'903, .deployed = 4'611'686'018'427'387'904, .sharesTotal = 9'223'372'036'854'775'807}, .assetsMaximum = 9'223'372'036'854'775'807, .expected = tesSUCCESS},
    };
    static constexpr SetCase kMaximumBelowTotalIou[] = {
        // available 9'999'999'999'999'999, deployed 0, maximum 9'999'999'999'999'999
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'999'999'999'999'997, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'999, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        // available 1, deployed 9'999'999'999'999'998, maximum 9'999'999'999'999'999
        {.vault = {.deployed = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.deployed = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 1, .deployed = 9'999'999'999'999'998, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        // available 9'999'999'999'999'998, deployed 1, maximum 9'999'999'999'999'999
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 9'999'999'999'999'996, .deployed = 1, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'997, .deployed = 1, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 9'999'999'999'999'998, .deployed = 1, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        // available 4'999'999'999'999'999, deployed 5'000'000'000'000'000, maximum 9'999'999'999'999'999
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'997, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'998, .expected = tecLIMIT_EXCEEDED},
        {.vault = {.available = 4'999'999'999'999'997, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'997}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'998, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'998}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {.available = 4'999'999'999'999'999, .deployed = 5'000'000'000'000'000, .sharesTotal = 9'999'999'999'999'999}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS},
    };
    static constexpr SetCase kMaximumGrid[] = {
        // 1'000'000'000'000'000e-15 grid steps
        {.vault = {}, .assetsMaximum = 999'999'999'999'998, .expected = tecPRECISION_LOSS, .exponent = -15},
        {.vault = {}, .assetsMaximum = 999'999'999'999'999, .expected = tecPRECISION_LOSS, .exponent = -15},
        {.vault = {}, .assetsMaximum = 1'000'000'000'000'000, .expected = tesSUCCESS, .exponent = -15},
        {.vault = {}, .assetsMaximum = 1'000'000'000'000'001, .expected = tecPRECISION_LOSS, .exponent = -15},
        {.vault = {}, .assetsMaximum = 1'000'000'000'000'002, .expected = tecPRECISION_LOSS, .exponent = -15},
        // 1'000'000'000'000'000e-6 grid steps
        {.vault = {}, .assetsMaximum = 999'999'999'999'998, .expected = tecPRECISION_LOSS, .exponent = -6},
        {.vault = {}, .assetsMaximum = 999'999'999'999'999, .expected = tecPRECISION_LOSS, .exponent = -6},
        {.vault = {}, .assetsMaximum = 1'000'000'000'000'000, .expected = tesSUCCESS, .exponent = -6},
        {.vault = {}, .assetsMaximum = 1'000'000'000'000'001, .expected = tecPRECISION_LOSS, .exponent = -6},
        {.vault = {}, .assetsMaximum = 1'000'000'000'000'002, .expected = tecPRECISION_LOSS, .exponent = -6},
        // 9'999'999'999'999'999e0 grid steps
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'000, .expected = tesSUCCESS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'001, .expected = tecPRECISION_LOSS, .exponent = 0},
        // 10'000'000'000'000'010e0 grid steps
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'008, .expected = tecPRECISION_LOSS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'009, .expected = tecPRECISION_LOSS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'010, .expected = tesSUCCESS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'011, .expected = tecPRECISION_LOSS, .exponent = 0},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'012, .expected = tecPRECISION_LOSS, .exponent = 0},
        // 9'999'999'999'999'999e79 grid steps
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS, .exponent = 79},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS, .exponent = 79},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS, .exponent = 79},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'000, .expected = tesSUCCESS, .exponent = 79},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'001, .expected = tecPRECISION_LOSS, .exponent = 79},
    };
    static constexpr SetCase kMaximumRangeXrp[] = {
        // 100'000'000'000'000'000e0 vault units
        {.vault = {}, .assetsMaximum = 99'999'999'999'999'998, .expected = tesSUCCESS},
        {.vault = {}, .assetsMaximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.vault = {}, .assetsMaximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        {.vault = {}, .assetsMaximum = 100'000'000'000'000'001, .expected = tecPRECISION_LOSS},
        {.vault = {}, .assetsMaximum = 100'000'000'000'000'002, .expected = tecPRECISION_LOSS},
    };
    static constexpr SetCase kMaximumRangeMpt[] = {
        // 922'337'203'685'477'580e1 vault units
        {.vault = {}, .assetsMaximum = 922'337'203'685'477'578, .expected = tesSUCCESS, .exponent = 1},
        {.vault = {}, .assetsMaximum = 922'337'203'685'477'579, .expected = tesSUCCESS, .exponent = 1},
        {.vault = {}, .assetsMaximum = 922'337'203'685'477'580, .expected = tesSUCCESS, .exponent = 1},
        {.vault = {}, .assetsMaximum = 922'337'203'685'477'581, .expected = tecPRECISION_LOSS, .exponent = 1},
        {.vault = {}, .assetsMaximum = 922'337'203'685'477'582, .expected = tecPRECISION_LOSS, .exponent = 1},
    };
    static constexpr SetCase kMaximumRangeIouScale0[] = {
        // 9'999'999'999'999'999e80 vault units
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS, .exponent = 80},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS, .exponent = 80},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS, .exponent = 80},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'000, .expected = tecPRECISION_LOSS, .exponent = 80},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'001, .expected = tecPRECISION_LOSS, .exponent = 80},
    };
    static constexpr SetCase kMaximumRangeIouScale6[] = {
        // 9'999'999'999'999'999e86 vault units
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS, .exponent = 86},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS, .exponent = 86},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS, .exponent = 86},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'000, .expected = tecPRECISION_LOSS, .exponent = 86},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'001, .expected = tecPRECISION_LOSS, .exponent = 86},
    };
    static constexpr SetCase kMaximumRangeIouScale10[] = {
        // 9'999'999'999'999'999e90 vault units
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'997, .expected = tesSUCCESS, .exponent = 90},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'998, .expected = tesSUCCESS, .exponent = 90},
        {.vault = {}, .assetsMaximum = 9'999'999'999'999'999, .expected = tesSUCCESS, .exponent = 90},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'000, .expected = tecPRECISION_LOSS, .exponent = 90},
        {.vault = {}, .assetsMaximum = 10'000'000'000'000'001, .expected = tecPRECISION_LOSS, .exponent = 90},
    };
    // clang-format on

    // Runs every list on the vaults staged open-ended or, when `closed`, closed-ended in
    // Subscription (VaultSet has no phase logic).
    void
    runSetBoundaries(jtx::Env& env, Setup const& s, bool closed)
    {
        std::uint32_t const p = parentCloseTime(env);
        auto const run =
            [&](std::string const& name, TestVaults const& vaults, std::span<SetCase const> cases) {
                for (Keylet const& vault : vaults)
                {
                    beginCase(("set " + vaultName(env, vault) + " " + name +
                               (closed ? ", closed-ended" : ""))
                                  .c_str());
                    int const scale = env.le(vault)->at(sfScale);
                    for (auto const& [row, assetsMaximum, expected, exponent] : cases)
                    {
                        StagedVault staged = row;
                        if (closed)
                        {
                            staged.subscriptionDate = p + 1'000;
                            staged.redemptionDate = p + 1'001'000;
                        }
                        expectSet(
                            env,
                            vault,
                            s.owner,
                            stagedAmounts(env, vault, staged),
                            Number{assetsMaximum, exponent - scale},
                            sampleText(staged),
                            expected);
                    }
                }
            };

        run("maximum below total", s.all, kMaximumBelowTotal);
        run("maximum below total, largest total", s.xrp, kMaximumBelowTotalXrp);
        run("maximum below total, largest total", s.mpt, kMaximumBelowTotalMpt);
        run("maximum below total, largest total", s.ious, kMaximumBelowTotalIou);
        run("maximum grid", s.ious, kMaximumGrid);
        run("maximum range", s.xrp, kMaximumRangeXrp);
        run("maximum range", s.mpt, kMaximumRangeMpt);
        run("maximum range", s.iouMinScale, kMaximumRangeIouScale0);
        run("maximum range", s.iouDefaultScale, kMaximumRangeIouScale6);
        run("maximum range", s.iouMaxScale, kMaximumRangeIouScale10);
    }

    void
    testSetBoundaries(jtx::Env& env, Setup const& s)
    {
        runSetBoundaries(env, s, false);
    }

    void
    testClosedEndedSetBoundaries(jtx::Env& env, Setup const& s)
    {
        runSetBoundaries(env, s, true);
    }

    void
    runTests() override
    {
        jtx::Env env{*this, vaultTestAmendments()};
        Setup const s = setup(env);

        runVaultSet(env, s.xrpVault, s.owner, 0, 0, tesSUCCESS);
        runVaultSet(env, s.xrpVault, s.owner, 0, 100, tesSUCCESS);
        runVaultSet(env, s.xrpVault, s.owner, 100, 0, tesSUCCESS);
        runVaultSet(env, s.xrpVault, s.owner, 100, 99, tecLIMIT_EXCEEDED);
        runVaultSet(env, s.xrpVault, s.owner, 100, 100, tesSUCCESS);
        runVaultSet(env, s.xrpVault, s.owner, 100, 101, tesSUCCESS);
        // An XRP cap above the native maximum is not representable as an amount.
        runVaultSet(env, s.xrpVault, s.owner, 0, 1'000'000'000'000'000'000, tecPRECISION_LOSS);
        testCapOffGrid(env, s.iouDefaultScaleVault, s.owner);

        runBlockDeposit(true, true, tesSUCCESS);
        runBlockDeposit(true, false, tesSUCCESS);
        runBlockDeposit(false, true, tecNO_PERMISSION);
        runBlockDeposit(false, false, tecNO_PERMISSION);
        testBothDepositFlags(env, s.xrpVault, s.owner);

        testSetBoundaries(env, s);

        testSetInInvestment(env, s.iouDefaultScaleVault, s.owner, s.holder);
        testClosedEndedSetBoundaries(env, s);

        // Known discrepancies, each fails until the C++ code is fixed.
        // clang-format off
        // testAssetsMaximumRoundedToGrid();  // FV_M2_19_b: AssetsMaximum over 16 digits is rounded
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultSet, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
