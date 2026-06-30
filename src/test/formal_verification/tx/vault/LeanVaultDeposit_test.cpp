#include <test/formal_verification/common/LeanSuite.h>
#include <test/jtx.h>

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
    }

    void
    runTests() override
    {
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test
