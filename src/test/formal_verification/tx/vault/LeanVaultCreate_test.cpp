#include <test/formal_verification/common/LeanSuite.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/pay.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>

#include <string>

namespace xrpl::test::formal_verification {

class LeanVaultCreate_test : public LeanSuite
{
    // Finding (FV_M2_19, c++): VaultCreate rounds an AssetsMaximum over 16 digits to the STAmount
    // grid via associateAsset, so the stored cap differs from the submitted value.
    void
    testAssetsMaximumRoundedToGrid()
    {
        using namespace jtx;
        testcase("AssetsMaximum over 16 digits is rounded on VaultCreate");

        Env env(*this);
        Account const owner{"owner"}, issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        PrettyAsset const asset = issuer["USD"];
        env.trust(asset(1'000), owner);
        env(pay(issuer, owner, asset(200)));
        env.close();

        Number const submitted{12'345'678'901'234'567LL, -1};  // 17 significant digits
        jtx::Vault vault{env};
        auto [tx, vaultKeylet] = vault.create({.owner = owner, .asset = asset.raw()});
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
        // Known discrepancies, each fails until the C++ code is fixed.
        // clang-format off
        // testAssetsMaximumRoundedToGrid();  // FV_M2_19: AssetsMaximum over 16 digits is rounded
        // clang-format on
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultCreate, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
