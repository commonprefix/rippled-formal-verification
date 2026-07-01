#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/deposit.h>
#include <test/formal_verification/ffi/vault/state.h>
#include <test/jtx.h>
#include <test/jtx/ter.h>

#include <xrpl/protocol/TER.h>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultDeposit_test : public LeanSuite
{
    Keylet static createVault(
        jtx::Env& env,
        jtx::Account const& owner,
        std::optional<std::uint32_t> flags = {})
    {
        jtx::Vault vault{env};
        auto const [jv, keylet] =
            vault.create({.owner = owner, .asset = xrpIssue(), .flags = flags});
        env(jv);
        env.close();
        return keylet;
    }

    void
    testCanDeposit()
    {
        using namespace jtx;
        Env env(*this);

        auto state = VaultState{
            .assetsTotal = Number{0},
            .accountBalance = XRP(1000),
            .asset = xrpIssue(),
        };
        auto amount = XRP(1000);

        Account const owner{"owner"};
        env.fund(XRP(10000), owner);
        auto const vaultKeylet = createVault(env, owner);

        TER const leanResult = leanCanDeposit(state, amount, false);

        env(Vault::deposit({
                .depositor = owner,
                .id = vaultKeylet.key,
                .amount = amount,
            }),
            jtx::Ter(
                std::ignore));  // ignore the result of the tx here to get it with env.ter() below
        TER const cppTer = env.ter();

        env.close();

        BEAST_EXPECT(cppTer == leanResult);
        BEAST_EXPECT(cppTer == tesSUCCESS);
    }

    void
    runTests() override
    {
        testCanDeposit();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test
