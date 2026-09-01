#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/LawfulVaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultDeleteFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultDelete_test : public LeanSuite
{
    void
    runVaultDelete(std::int64_t available, std::int64_t total, std::int64_t shares, TER expected)
    {
        using namespace jtx;
        testcase(
            "delete available=" + std::to_string(available) + " total=" + std::to_string(total) +
            " shares=" + std::to_string(shares));

        Env env(*this);
        Account const owner{"owner"};
        PrettyAsset const asset{xrpIssue(), 1'000'000};
        env.fund(XRP(1'000'000), owner);
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        BEAST_EXPECT(updateVaultState(
            env,
            vaultKeylet,
            Number{total},
            Number{available},
            static_cast<std::uint64_t>(shares)));

        LawfulVault const state = readVaultState(env, vaultKeylet, asset.raw());
        auto const lean = leanCanVaultDelete(state);
        expectLawful(lean);
        TER const leanTer = lean.ter;

        env(Vault::del({.owner = owner, .id = vaultKeylet.key}), jtx::Ter(std::ignore));
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
    testEmptyVaultDeletes()
    {
        runVaultDelete(0, 0, 0, tesSUCCESS);
    }

    void
    testSharesBlockDelete()
    {
        runVaultDelete(0, 0, 5, tecHAS_OBLIGATIONS);
    }

    void
    testTotalAndSharesBlockDelete()
    {
        runVaultDelete(0, 5, 5, tecHAS_OBLIGATIONS);
    }

    void
    testAllFieldsBlockDelete()
    {
        runVaultDelete(5, 5, 5, tecHAS_OBLIGATIONS);
    }

    void
    runTests() override
    {
        testEmptyVaultDeletes();
        testSharesBlockDelete();
        testTotalAndSharesBlockDelete();
        testAllFieldsBlockDelete();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDelete, formal_verification, xrpl);

}  // namespace xrpl::test
