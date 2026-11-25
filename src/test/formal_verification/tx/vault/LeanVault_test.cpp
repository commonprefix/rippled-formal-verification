#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/basics/Number.h>

#include <functional>
#include <optional>
#include <string>
#include <utility>

namespace xrpl::test::formal_verification {

// A not-lawful result is the expected and each case violates one invariant clause
// (RawVault.WF / RawVault.Valid) and build must reject it.
class LeanVault_test : public LeanSuite
{
    // A valid vault: solvent, open-ended, fractional (IOU) asset at scale 6, no cap, no loans.
    static Vault
    baseline()
    {
        return {
            .assetsAvailable = Number{5},
            .assetsMaximum = std::nullopt,
            .numericType = 2,
            .scale = 6,
            .sharesTotal = Number{1'000'000}};
    }

    // A closed-ended vault with the minimum 180 s investment period and an early-exit fee.
    static Vault
    closedEnded()
    {
        auto s = baseline();
        s.subscriptionDate = 1'000;
        s.redemptionDate = 1'180;
        s.earlyExitFeeRate = 5'000;
        return s;
    }

    using Mutation = std::function<void(Vault&)>;

    // `mutate` applied to `start`: build accepts the vault or rejects it.
    void
    expectValid(std::string const& label, Mutation const& mutate = {}, Vault start = baseline())
    {
        expectBuild(label, mutate, std::move(start), true);
    }

    void
    expectInvalid(std::string const& label, Mutation const& mutate = {}, Vault start = baseline())
    {
        expectBuild(label, mutate, std::move(start), false);
    }

    void
    expectBuild(std::string const& label, Mutation const& mutate, Vault vault, bool valid)
    {
        if (mutate)
            mutate(vault);
        testcase(label);
        BEAST_EXPECTS(VaultFFI::build(vault).has_value() == valid, label);
    }

    void
    testLawful()
    {
        expectValid("valid baseline");
        expectValid("lent-out vault with loss, reserve and yield", [](Vault& vault) {
            vault.assetsDeployed = Number{3};
            vault.assetsReserved = Number{2};
            vault.lossUnrealized = Number{3};
            vault.yieldUnrealized = Number{1};
        });
        expectValid("closed-ended vault with an early-exit fee", {}, closedEnded());
        expectValid("deposits blocked by an owner allowed to", [](Vault& vault) {
            vault.ownerCanBlockDeposit = true;
            vault.depositBlocked = true;
        });
        // The cap is a transaction check now, not a vault invariant.
        expectValid("assetsTotal above assetsMaximum", [](Vault& vault) {
            vault.assetsMaximum = Number{3};
        });
        expectValid("sharesTotal just below INT64_MAX", [](Vault& vault) {
            vault.sharesTotal = Number{9'223'372'036'854'775LL, 3};  // 16 digits, below INT64_MAX
        });
    }

    // RawVault.WF clauses (the *_norm clauses are omitted)
    void
    testWellFormed()
    {
        expectInvalid("negative sharesTotal", [](Vault& vault) { vault.sharesTotal = Number{-5}; });
        expectInvalid("fractional sharesTotal", [](Vault& vault) {
            vault.sharesTotal = Number{15, -1};  // 1.5, not an integer
        });
        expectInvalid("integral asset with nonzero scale", [](Vault& vault) {
            vault.numericType = 1;  // int64 (MPT) asset must have scale 0
            vault.scale = 3;
        });
        expectInvalid("scale above 10", [](Vault& vault) { vault.scale = 11; });
    }

    // RawVault.Valid clauses.
    void
    testValid()
    {
        expectInvalid(
            "negative assetsAvailable", [](Vault& vault) { vault.assetsAvailable = Number{-1}; });
        expectInvalid(
            "negative assetsDeployed", [](Vault& vault) { vault.assetsDeployed = Number{-1}; });
        expectInvalid(
            "negative assetsReserved", [](Vault& vault) { vault.assetsReserved = Number{-1}; });
        expectInvalid(
            "negative lossUnrealized", [](Vault& vault) { vault.lossUnrealized = Number{-1}; });
        expectInvalid(
            "negative yieldUnrealized", [](Vault& vault) { vault.yieldUnrealized = Number{-1}; });
        // Total and available are 0 so only assetsMaximum_pos fails.
        expectInvalid("assetsMaximum is zero", [](Vault& vault) {
            vault.assetsAvailable = Number{0};
            vault.sharesTotal = Number{0};
            vault.assetsMaximum = Number{0};
        });
        expectInvalid("zero shares with available assets", [](Vault& vault) {
            vault.sharesTotal = Number{0};
        });
        expectInvalid("zero shares with deployed assets", [](Vault& vault) {
            vault.assetsAvailable = Number{0};
            vault.assetsDeployed = Number{5};
            vault.sharesTotal = Number{0};
        });
        expectInvalid("lossUnrealized above assetsDeployed", [](Vault& vault) {
            vault.assetsDeployed = Number{2};
            vault.lossUnrealized = Number{3};
        });
        expectInvalid("assetsReserved above assetsDeployed", [](Vault& vault) {
            vault.assetsDeployed = Number{2};
            vault.assetsReserved = Number{3};
        });
        // The share supply is an int64.
        expectInvalid(
            "sharesTotal above INT64_MAX", [](Vault& vault) { vault.sharesTotal = Number{1, 19}; });
        // 17 significant digits do not fit an IOU STAmount.
        expectInvalid("assetsDeployed not representable", [](Vault& vault) {
            vault.assetsDeployed = Number{12'345'678'901'234'567LL};
        });
        // On the grid (a multiple of 10^0) but 17 digits.
        expectInvalid("assetsAvailable not representable", [](Vault& vault) {
            vault.assetsAvailable = Number{12'345'678'901'234'567LL};
        });
        // Representable but below the scale-6 grid.
        expectInvalid("assetsAvailable off the vault grid", [](Vault& vault) {
            vault.assetsAvailable = Number{5, -7};
        });
        // Exactly one grid step: lawful, so the row above fails on the grid clause alone.
        expectValid("assetsAvailable on the vault grid", [](Vault& vault) {
            vault.assetsAvailable = Number{5, -6};
        });
        expectInvalid("deposits blocked by an owner not allowed to", [](Vault& vault) {
            vault.depositBlocked = true;
        });
        expectInvalid(
            "investment period below 180 s",
            [](Vault& vault) { vault.redemptionDate = 1'179; },
            closedEnded());
        expectInvalid(
            "investment period of 30 years",
            [](Vault& vault) { vault.redemptionDate = 1'000 + 30u * 31'556'952u; },
            closedEnded());
        expectInvalid(
            "subscription date without a redemption date",
            [](Vault& vault) { vault.redemptionDate = std::nullopt; },
            closedEnded());
        expectInvalid("early-exit fee on an open-ended vault", [](Vault& vault) {
            vault.earlyExitFeeRate = 0;
        });
        expectInvalid(
            "early-exit fee above 100%",
            [](Vault& vault) { vault.earlyExitFeeRate = 100'001; },
            closedEnded());
    }

    void
    runTests() override
    {
        testLawful();
        testWellFormed();
        testValid();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVault, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
