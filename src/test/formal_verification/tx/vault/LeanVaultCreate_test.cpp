#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultCreateFFI.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>

#include <optional>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultCreate_test : public LeanSuite
{
    // Compare the on-ledger state VaultCreate wrote against the model's Vault.create, fed the
    // tx-level cap, the asset's numericType tag, and the scale read from the SLE.
    void
    compareCreatedVault(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        Asset const& asset,
        std::optional<Number> const& assetsMaximum)
    {
        VaultState const cpp = readVaultState(env, vaultKeylet, asset);
        VaultState const lean = leanVaultCreate(
            assetsMaximum.has_value(),
            assetsMaximum.value_or(Number{0}),
            NumericTypeFFI::tagOf(asset),
            cpp.scale);

        BEAST_EXPECT(lean.assetsTotal == cpp.assetsTotal);
        BEAST_EXPECT(lean.assetsAvailable == cpp.assetsAvailable);
        BEAST_EXPECT(lean.hasMaximum == cpp.hasMaximum);
        BEAST_EXPECT(lean.assetsMaximum == cpp.assetsMaximum);
        BEAST_EXPECT(lean.numericType == cpp.numericType);
        BEAST_EXPECT(lean.scale == cpp.scale);
        BEAST_EXPECT(lean.sharesTotal == cpp.sharesTotal);
        BEAST_EXPECT(lean.lossUnrealized == cpp.lossUnrealized);
    }

    void
    testCreateXRP()
    {
        using namespace jtx;
        testcase("create XRP vault");

        Env env(*this);
        Account const owner{"owner"};
        env.fund(XRP(1'000'000), owner);
        env.close();

        PrettyAsset const asset{xrpIssue(), 1'000'000};
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        compareCreatedVault(env, vaultKeylet, asset.raw(), std::nullopt);
    }

    // MPT asset: covers the remaining numericType tag together with a nonzero cap.
    void
    testCreateMPTWithMaximum()
    {
        using namespace jtx;
        testcase("create MPT vault with assetsMaximum");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        PrettyAsset const asset = mptt.issuanceID();
        env.close();

        Vault vault{env};
        auto [tx, vaultKeylet] = vault.create({.owner = owner, .asset = asset.raw()});
        Number const cap{1'000};
        tx[sfAssetsMaximum] = cap;
        env(tx);
        env.close();

        compareCreatedVault(env, vaultKeylet, asset.raw(), cap);
    }

    // IOU asset: exercises the nonzero default vault scale.
    void
    testCreateIOU()
    {
        using namespace jtx;
        testcase("create IOU vault");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        compareCreatedVault(env, vaultKeylet, asset.raw(), std::nullopt);
    }

    void
    runTests() override
    {
        testCreateXRP();
        testCreateMPTWithMaximum();
        testCreateIOU();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultCreate, formal_verification, xrpl);

}  // namespace xrpl::test
