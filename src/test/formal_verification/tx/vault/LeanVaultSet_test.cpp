#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultSetFFI.h>
#include <test/formal_verification/tx/vault/CreateSetSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>
#include <test/jtx/ter.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <cstdint>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

class LeanVaultSet_test : public LeanSuite
{
    // VaultSet of `cap` on `staged`, applied on a throwaway copy of the open ledger, and the model
    // on the same pre-state; returns the C++ verdict.
    TER
    checkSet(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& owner,
        StagedVault const& staged,
        Number const& cap)
    {
        auto tx = jtx::Vault::set({.owner = owner, .id = vault.key});
        tx[sfAssetsMaximum] = cap;
        AppliedVaultTx const cpp = applyStaged(env, vault, owner, staged, tx);
        auto const lean = leanCanVaultUpdate(cpp.pre, cap);
        expectLawful(lean);
        std::string const at = "total " + to_string(cpp.pre.assetsTotal) + " cap " +
            to_string(cap) + " cpp=" + transToken(cpp.ter) + ": ";
        BEAST_EXPECTS(lean.ter == cpp.ter, at + "lean=" + transToken(lean.ter));
        if (cpp.ter != tesSUCCESS || lean.ter != tesSUCCESS)
            return cpp.ter;

        // A zero cap is stored as no cap on both sides.
        LeanUpdateResult const updated = leanVaultUpdate(cpp.pre, cap);
        BEAST_EXPECTS(!updated.leanError.has_value(), at + "lean update error");
        BEAST_EXPECTS(
            updated.vault.assetsMaximum == cpp.post.assetsMaximum,
            at + "assetsMaximum lean=" +
                (updated.vault.assetsMaximum ? to_string(*updated.vault.assetsMaximum) : "none") +
                " cpp=" + (cpp.post.assetsMaximum ? to_string(*cpp.post.assetsMaximum) : "none"));
        return cpp.ter;
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
            .available = gridUnits(env, xrpVault, assetsTotal),
            .sharesTotal = static_cast<std::uint64_t>(assetsTotal)};
        TER const cppTer = checkSet(env, xrpVault, owner, staged, Number{assetsMaximum});
        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
    }

    // Deposit blocking: only a vault created with tfVaultOwnerCanBlockDeposit accepts the flags.
    void
    runBlockDeposit(bool ownerCanBlock, bool block, TER expected)
    {
        using namespace jtx;
        testcase(
            std::string(block ? "block" : "unblock") + " deposits, owner " +
            (ownerCanBlock ? "can" : "cannot") + " block");

        Env env(*this);
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
        LeanUpdateResult const updated = leanVaultUpdate(state, std::nullopt, block, !block);

        env(jtx::Vault::set(
                {.owner = owner,
                 .id = vaultKeylet.key,
                 .flags = block ? tfVaultDepositBlock : tfVaultDepositUnblock}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Vault const cpp = readVaultState(env, vaultKeylet, xrpIssue());
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            lean.ter == cppTer,
            std::string("lean=") + transToken(lean.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return;
        BEAST_EXPECTS(!updated.leanError.has_value(), "lean update error");
        BEAST_EXPECTS(
            updated.vault.depositBlocked == cpp.depositBlocked && cpp.depositBlocked == block,
            std::string("depositBlocked lean=") + (updated.vault.depositBlocked ? "1" : "0") +
                " cpp=" + (cpp.depositBlocked ? "1" : "0"));
    }

    // An IOU cap below the vault grid is rejected on both sides. Covered by testMaximumGridSweep.
    void
    testCapOffGrid(jtx::Env& env, Keylet const& iouVault, jtx::Account const& owner)
    {
        testcase("set an IOU cap off the vault grid");
        TER const cppTer = checkSet(
            env, iouVault, owner, {.available = gridUnits(env, iouVault, 0)}, Number{1, -7});
        BEAST_EXPECTS(cppTer == tecPRECISION_LOSS, std::string("cpp=") + transToken(cppTer));
    }

    void
    testEmptyVaultUnlimited(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        runVaultSet(env, xrpVault, owner, 0, 0, tesSUCCESS);
    }

    void
    testEmptyVaultWithCap(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        runVaultSet(env, xrpVault, owner, 0, 100, tesSUCCESS);
    }

    void
    testUnlimitedCap(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        runVaultSet(env, xrpVault, owner, 100, 0, tesSUCCESS);
    }

    // Covered by testMaximumBelowTotalSweep (with testCapEqualsTotal, testCapAboveTotal).
    void
    testCapBelowTotal(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        runVaultSet(env, xrpVault, owner, 100, 99, tecLIMIT_EXCEEDED);
    }

    void
    testCapEqualsTotal(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        runVaultSet(env, xrpVault, owner, 100, 100, tesSUCCESS);
    }

    void
    testCapAboveTotal(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        runVaultSet(env, xrpVault, owner, 100, 101, tesSUCCESS);
    }

    // An XRP cap above the native maximum is not representable as an amount. Covered by
    // testXrpMaximumSweep.
    void
    testCapNotRepresentable(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        runVaultSet(env, xrpVault, owner, 0, 1'000'000'000'000'000'000, tecPRECISION_LOSS);
    }

    // Finding (FV_M2_19, c++): VaultSet rounds an AssetsMaximum over 16 digits to the STAmount
    // grid via associateAsset, so the stored cap differs from the submitted value.
    void
    testAssetsMaximumRoundedToGrid()
    {
        using namespace jtx;
        testcase("AssetsMaximum over 16 digits is rounded on VaultSet");

        Env env(*this);
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

    // ---- Sweeps --------------------------------------------------------------------------------

    using SweepVaults = std::vector<Keylet>;

    void
    testMaximumBelowTotalSweep(jtx::Env& env, jtx::Account const& owner, SweepVaults const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            sweepMaximumBelowTotal(env, vault, owner);
        }
    }

    // A non-zero maximum below the assets total is tecLIMIT_EXCEEDED; 0 removes the cap. Rows set
    // the maximum to the total, split between available and deployed assets.
    void
    sweepMaximumBelowTotal(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        beginCase(("set " + vaultName(env, vault) + " maximum below total-Sweep").c_str());
        runAroundCusp(kSetMaximumCases, [&](SetMaximumCusp const& c) {
            StagedVault const staged{
                .available = gridUnits(env, vault, c.available),
                .deployed = gridUnits(env, vault, c.deployed),
                .sharesTotal = static_cast<std::uint64_t>(c.available + c.deployed)};
            return checkSet(env, vault, owner, staged, Number{gridUnits(env, vault, c.maximum)});
        });
    }

    void
    testMaximumGridSweep(jtx::Env& env, jtx::Account const& owner, SweepVaults const& ious)
    {
        for (Keylet const& vault : ious)
        {
            sweepMaximumGrid(env, vault, owner);
        }
    }

    // An IOU maximum off the vault grid 10^-scale, or with more than 16 digits, is
    // tecPRECISION_LOSS. Rows are on the grid of an empty vault; moving the mantissa leaves it.
    void
    sweepMaximumGrid(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        beginCase(("set " + vaultName(env, vault) + " maximum grid-Sweep").c_str());
        int const scale = env.le(vault)->at(sfScale);
        runAroundCusp(kMaximumGridCases, [&](MaximumGridCusp const& c) {
            Number const cap{c.mantissa, static_cast<int>(c.exponent) - scale};
            return checkSet(env, vault, owner, {.available = gridUnits(env, vault, 0)}, cap);
        });
    }

    // An XRP maximum above 1e17 drops is not representable (tecPRECISION_LOSS on both sides).
    void
    testXrpMaximumSweep(jtx::Env& env, Keylet const& xrpVault, jtx::Account const& owner)
    {
        beginCase("set XRP maximum range-Sweep");
        runAroundCusp(kXrpMaximumCases, [&](std::int64_t drops) {
            return checkSet(
                env, xrpVault, owner, {.available = gridUnits(env, xrpVault, 0)}, Number{drops});
        });
    }

    void
    runTests() override
    {
        using namespace jtx;
        // One ledger holding a vault per asset; every staged VaultSet runs on a throwaway view.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        env.close();
        Asset const iou = issuer["USD"].asset();
        Keylet const xrpVault = create_set_sweep::createVaultAt(env, owner, xrpIssue());
        Keylet const mptVault = create_set_sweep::createVaultAt(env, owner, mptt.issuanceID());
        Keylet const iouScale0Vault = create_set_sweep::createVaultAt(env, owner, iou, 0);
        Keylet const iouScale6Vault = create_set_sweep::createVaultAt(env, owner, iou, 6);
        Keylet const iouScale10Vault = create_set_sweep::createVaultAt(env, owner, iou, 10);

        testEmptyVaultUnlimited(env, xrpVault, owner);
        testEmptyVaultWithCap(env, xrpVault, owner);
        testUnlimitedCap(env, xrpVault, owner);
        testCapBelowTotal(env, xrpVault, owner);
        testCapEqualsTotal(env, xrpVault, owner);
        testCapAboveTotal(env, xrpVault, owner);
        testCapNotRepresentable(env, xrpVault, owner);
        testCapOffGrid(env, iouScale6Vault, owner);

        runBlockDeposit(true, true, tesSUCCESS);
        runBlockDeposit(true, false, tesSUCCESS);
        runBlockDeposit(false, true, tecNO_PERMISSION);
        runBlockDeposit(false, false, tecNO_PERMISSION);

        SweepVaults const ious{iouScale0Vault, iouScale6Vault, iouScale10Vault};
        SweepVaults const all{xrpVault, mptVault, iouScale0Vault, iouScale6Vault, iouScale10Vault};
        testMaximumBelowTotalSweep(env, owner, all);
        testMaximumGridSweep(env, owner, ious);
        testXrpMaximumSweep(env, xrpVault, owner);

        // Known discrepancies, each fails until the C++ code is fixed.
        // clang-format off
        // testAssetsMaximumRoundedToGrid();  // FV_M2_19_b: AssetsMaximum over 16 digits is rounded
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultSet, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
