#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultSetFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <cstdint>
#include <string>

namespace xrpl::test::formal_verification {

class LeanVaultSet_test : public LeanSuite
{
    void
    runVaultSet(std::int64_t assetsTotal, std::int64_t assetsMaximum, TER expected)
    {
        using namespace jtx;
        testcase(
            "set max=" + std::to_string(assetsMaximum) + " total=" + std::to_string(assetsTotal));

        Env env(*this);
        Account const owner{"owner"};
        PrettyAsset const asset{xrpIssue(), 1'000'000};
        env.fund(XRP(1'000'000), owner);
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        BEAST_EXPECT(updateVaultState(
            env,
            vaultKeylet,
            Number{assetsTotal},
            Number{assetsTotal},
            static_cast<std::uint64_t>(assetsTotal)));

        Vault const state = readVaultState(env, vaultKeylet, asset.raw());
        Number const cap{assetsMaximum};
        auto const lean = leanCanVaultUpdate(state, cap);
        expectLawful(lean);
        TER const leanTer = lean.ter;
        LeanUpdateResult const updated = leanVaultUpdate(state, cap);

        auto tx = jtx::Vault::set({.owner = owner, .id = vaultKeylet.key});
        tx[sfAssetsMaximum] = cap;
        env(tx, jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        Vault const cpp = readVaultState(env, vaultKeylet, asset.raw());
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            leanTer == cppTer,
            std::string("lean=") + transToken(leanTer) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return;

        // A zero cap is stored as no cap on both sides.
        BEAST_EXPECTS(!updated.leanError.has_value(), "lean update error");
        BEAST_EXPECTS(
            updated.vault.assetsMaximum == cpp.assetsMaximum,
            "assetsMaximum lean=" +
                (updated.vault.assetsMaximum ? to_string(*updated.vault.assetsMaximum) : "none") +
                " cpp=" + (cpp.assetsMaximum ? to_string(*cpp.assetsMaximum) : "none"));
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
        if (!block)
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

    // An IOU cap below the vault grid is rejected on both sides.
    void
    testCapOffGrid()
    {
        using namespace jtx;
        testcase("set an IOU cap off the vault grid");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());

        Vault const state = readVaultState(env, vaultKeylet, asset.raw());
        Number const cap{1, -7};
        auto const lean = leanCanVaultUpdate(state, cap);
        expectLawful(lean);

        auto tx = jtx::Vault::set({.owner = owner, .id = vaultKeylet.key});
        tx[sfAssetsMaximum] = cap;
        env(tx, jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();
        BEAST_EXPECTS(cppTer == tecPRECISION_LOSS, std::string("cpp=") + transToken(cppTer));
        BEAST_EXPECTS(lean.ter == cppTer, std::string("lean=") + transToken(lean.ter));
    }

    void
    testEmptyVaultUnlimited()
    {
        runVaultSet(0, 0, tesSUCCESS);
    }

    void
    testEmptyVaultWithCap()
    {
        runVaultSet(0, 100, tesSUCCESS);
    }

    void
    testUnlimitedCap()
    {
        runVaultSet(100, 0, tesSUCCESS);
    }

    void
    testCapBelowTotal()
    {
        runVaultSet(100, 99, tecLIMIT_EXCEEDED);
    }

    void
    testCapEqualsTotal()
    {
        runVaultSet(100, 100, tesSUCCESS);
    }

    void
    testCapAboveTotal()
    {
        runVaultSet(100, 101, tesSUCCESS);
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

    void
    runTests() override
    {
        testEmptyVaultUnlimited();
        testEmptyVaultWithCap();
        testUnlimitedCap();
        testCapBelowTotal();
        testCapEqualsTotal();
        testCapAboveTotal();
        testCapOffGrid();

        runBlockDeposit(true, true, tesSUCCESS);
        runBlockDeposit(true, false, tesSUCCESS);
        runBlockDeposit(false, true, tecNO_PERMISSION);

        // Known discrepancies, each fails until the C++ code is fixed.
        // clang-format off
        // testAssetsMaximumRoundedToGrid();  // FV_M2_19_b: AssetsMaximum over 16 digits is rounded
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultSet, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
