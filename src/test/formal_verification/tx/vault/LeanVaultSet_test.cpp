#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultSetFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

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
        auto const lean = leanCanVaultSet(state, cap);
        expectLawful(lean);
        TER const leanTer = lean.ter;

        auto tx = jtx::Vault::set({.owner = owner, .id = vaultKeylet.key});
        tx[sfAssetsMaximum] = cap;
        env(tx, jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            leanTer == cppTer,
            std::string("lean=") + transToken(leanTer) + " cpp=" + transToken(cppTer));
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

    void
    runTests() override
    {
        testEmptyVaultUnlimited();
        testEmptyVaultWithCap();
        testUnlimitedCap();
        testCapBelowTotal();
        testCapEqualsTotal();
        testCapAboveTotal();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultSet, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
