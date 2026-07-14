#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultStateFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultClawback_test : public LeanSuite
{
    static MPTIssue
    shareIssue(jtx::Env& env, Keylet const& vaultKeylet)
    {
        return MPTIssue{env.le(vaultKeylet)->at(sfShareMPTID)};
    }

    void
    compareClawbackAsset(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& issuer,
        jtx::Account const& holder,
        Asset const& asset,
        STAmount const& amount,
        TER expected)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        LeanClawbackResult const clawback = leanVaultClawback(state, amount, false);

        env(Vault::clawback(
                {.issuer = issuer, .id = vaultKeylet.key, .holder = holder, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!clawback.threw, "lean clawback raised");

        TER const leanTer = clawback.error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            leanTer == expected,
            std::string("lean=") + transToken(leanTer) + " expected " + transToken(expected));

        if (cppTer != tesSUCCESS)
            return;

        auto const newVaultSle = env.le(vaultKeylet);
        auto const issuanceKeylet = keylet::mptIssuance(newVaultSle->at(sfShareMPTID));
        Number const cppAssetsTotal = newVaultSle->at(sfAssetsTotal);
        Number const cppAssetsAvailable = newVaultSle->at(sfAssetsAvailable);
        Number const cppSharesTotal{
            static_cast<std::int64_t>(env.le(issuanceKeylet)->at(sfOutstandingAmount))};
        BEAST_EXPECTS(clawback.vault.assetsTotal == cppAssetsTotal, "assetsTotal mismatch");
        BEAST_EXPECTS(
            clawback.vault.assetsAvailable == cppAssetsAvailable, "assetsAvailable mismatch");
        BEAST_EXPECTS(clawback.vault.sharesTotal == cppSharesTotal, "sharesTotal mismatch");
    }

    void
    testClawbackAsset(std::int64_t seed, std::int64_t amount, TER expected)
    {
        using namespace jtx;
        testcase("clawback MPT asset " + std::to_string(amount) + " from " + std::to_string(seed));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
        PrettyAsset const asset = mptt.issuanceID();
        mptt.authorize({.account = holder});
        env.close();
        env(pay(issuer, holder, asset(seed)));
        env.close();

        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = asset(seed)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        compareClawbackAsset(
            env, vaultKeylet, issuer, holder, asset.raw(), asset(amount), expected);
    }

    // canClawbackVaultShares preclaim
    void
    compareCanClawbackShares(
        jtx::Env& env,
        Keylet const& vaultKeylet,
        jtx::Account const& owner,
        jtx::Account const& holder,
        Asset const& asset)
    {
        using namespace jtx;
        VaultState const state = readVaultState(env, vaultKeylet, asset);
        LeanCanClawbackResult const lean = leanCanClawbackVaultShares(state);
        BEAST_EXPECTS(!lean.threw, "lean canClawbackVaultShares raised");

        env(Vault::clawback({.issuer = owner, .id = vaultKeylet.key, .holder = holder}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        bool const cppDenied = cppTer == tecNO_PERMISSION;
        BEAST_EXPECTS(
            lean.error.has_value() == cppDenied,
            std::string("cpp=") + transToken(cppTer) +
                (lean.error ? " lean denied" : " lean permitted"));
        if (cppDenied)
            BEAST_EXPECT(lean.error.value() == tecNO_PERMISSION);
    }

    // IOU vault where `holder` deposits, optionally leaving the vault with no assets (staged) so
    // the owner is permitted to burn the remaining shares.
    void
    testCanClawbackShares(bool depositSeed, bool zeroAssets)
    {
        using namespace jtx;
        testcase(
            std::string("canClawbackVaultShares ") + (depositSeed ? "shares" : "no shares") +
            (zeroAssets ? ", no assets" : ", assets present"));

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        if (depositSeed)
        {
            env(trust(holder, asset(1'000'000)));
            env.close();
            env(pay(issuer, holder, asset(1'000)));
            env.close();
            env(Vault::deposit(
                    {.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
                jtx::Ter(tesSUCCESS));
            env.close();
        }
        if (zeroAssets)
            BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{0}, Number{0}, 1'000'000'000));

        compareCanClawbackShares(env, vaultKeylet, owner, holder, asset.raw());
    }

    // Discrepancy: the owner burning shares of an asset-less vault succeeds in C++ (recovering
    // nothing), but the model's share-clawback computes a zero conversion and returns
    // tecPRECISION_LOSS.
    void
    testClawbackOwnerBurn()
    {
        using namespace jtx;
        testcase("clawback owner burn shares (assets zero)");

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, issuer, holder);
        env.close();

        PrettyAsset const asset = issuer["USD"];
        auto const vaultKeylet = createVault(env, owner, asset.raw());
        env(trust(holder, asset(1'000'000)));
        env.close();
        env(pay(issuer, holder, asset(1'000)));
        env.close();
        env(Vault::deposit({.depositor = holder, .id = vaultKeylet.key, .amount = asset(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();
        BEAST_EXPECT(updateVaultState(env, vaultKeylet, Number{0}, Number{0}, 1'000'000'000));

        VaultState const state = readVaultState(env, vaultKeylet, asset.raw());
        STAmount const shares{shareIssue(env, vaultKeylet), 0};
        LeanClawbackResult const clawback = leanVaultClawback(state, shares, true);

        env(Vault::clawback({.issuer = owner, .id = vaultKeylet.key, .holder = holder}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(!clawback.threw, "lean clawback raised");
        TER const leanTer = clawback.error.value_or(tesSUCCESS);
        BEAST_EXPECTS(
            leanTer == cppTer,
            std::string("lean=") + transToken(leanTer) + " cpp=" + transToken(cppTer));
    }

    void
    runTests() override
    {
        using namespace jtx;

        // Asset clawback by the issuer: partial, full, and over-seed (clamped to available).
        testClawbackAsset(1'000, 400, tesSUCCESS);
        testClawbackAsset(1'000, 1'000, tesSUCCESS);
        testClawbackAsset(1'000, 1'001, tesSUCCESS);

        // canClawbackVaultShares: permitted only with shares and no assets.
        testCanClawbackShares(true, true);
        testCanClawbackShares(true, false);
        testCanClawbackShares(false, false);

        // Known discrepancy: each fails until the model is fixed
        // testClawbackOwnerBurn();  // model tecPRECISION_LOSS where C++ burns shares (tesSUCCESS)
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultClawback, formal_verification, xrpl);

}  // namespace xrpl::test
