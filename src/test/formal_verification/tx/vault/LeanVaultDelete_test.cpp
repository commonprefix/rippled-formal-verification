#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultDeleteFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>
#include <test/jtx/ter.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/chrono.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/TER.h>

#include <chrono>
#include <cstdint>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

struct DeleteCase
{
    StagedVault vault;
    TER expected;
};

class LeanVaultDelete_test : public LeanSuite
{
    // Every staged delete runs on a throwaway view of one shared ledger and expects its verdict on
    // both sides; on success the vault is gone.
    // Staged states may be unreachable by any transaction: a verdict compares model and C++ on the
    // same pre-state and does not claim the state is reachable (see stageVault).

    void
    runVaultDelete(
        jtx::Env& env,
        Keylet const& xrpVault,
        jtx::Account const& owner,
        std::int64_t available,
        std::int64_t total,
        std::int64_t shares,
        TER expected)
    {
        testcase(
            "delete available=" + std::to_string(available) + " total=" + std::to_string(total) +
            " shares=" + std::to_string(shares));
        StagedVault const staged{
            .available = available,
            .deployed = total - available,
            .sharesTotal = static_cast<std::uint64_t>(shares)};
        AppliedVaultDelete const cpp =
            applyDelete(env, xrpVault, owner, stagedAmounts(env, xrpVault, staged));
        auto const lean = leanCanVaultDelete(cpp.pre);
        expectLawful(lean);
        expectSame(*this, sampleText(staged), cpp, lean, expected);
    }

    // VaultDelete has no phase logic: an empty closed-ended vault is deleted during Investment.
    // A real vault on its own ledger, advanced into Investment.
    void
    testDeleteInInvestment()
    {
        using namespace jtx;
        using namespace std::chrono_literals;
        testcase("delete an empty closed-ended vault in investment");

        Env env{*this, vaultTestAmendments()};
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        Asset const asset = issuer["USD"].asset();

        NetClock::time_point const subscriptionDate =
            alignedTime(env, env.now() + kSubscriptionOffset);
        NetClock::time_point const redemptionDate =
            alignedTime(env, subscriptionDate + kInvestmentWindow);
        jtx::Vault const vault{env};
        auto const [createTx, vaultKeylet] = vault.create({
            .owner = owner,
            .asset = asset,
            .vaultKind = std::to_underlying(VaultKind::ClosedEnded),
            .subscriptionDate = timeCount(subscriptionDate),
            .redemptionDate = timeCount(redemptionDate),
            .earlyExitFeeRate = 5'000,
        });
        env(createTx);
        env.close();
        env.close(subscriptionDate + 1s);
        BEAST_EXPECTS(
            getVaultPhase(*env.current(), env.le(vaultKeylet)) == VaultPhase::Investment,
            "the vault is not in the investment phase");

        Vault const pre = readVaultState(env, vaultKeylet, asset);
        auto const lean = leanCanVaultDelete(pre);
        expectLawful(lean);
        env(jtx::Vault::del({.owner = owner, .id = vaultKeylet.key}), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();
        expectSame(
            *this,
            "closed-ended vault in investment: ",
            {.pre = pre, .ter = cppTer, .deleted = !env.le(vaultKeylet)},
            lean,
            tesSUCCESS);
    }

    using TestVaults = std::vector<Keylet>;

    struct Setup
    {
        jtx::Account owner;
        Keylet xrpVault;
        TestVaults all;
    };

    static Setup
    setup(jtx::Env& env)
    {
        using namespace jtx;
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        env.close();
        Asset const iou = issuer["USD"].asset();
        Keylet const xrpVault = createVault(env, owner, xrpIssue());
        return {
            .owner = owner,
            .xrpVault = xrpVault,
            .all =
                {
                    xrpVault,
                    createVault(env, owner, mptt.issuanceID()),
                    createVault(env, owner, iou, kVaultMinimumIouScale),
                    createVault(env, owner, iou, kVaultDefaultIouScale),
                    createVault(env, owner, iou, kFixedPrecisionVaultMaximumIouScale),
                },
        };
    }

    // Each case stages its vault, deletes it and expects its verdict on both sides.
    // - Obligations: only an empty vault with no shares can be deleted; assets or shares left are
    //   tecHAS_OBLIGATIONS. A vault with shares holds assets or is insolvent; no shares means no
    //   assets.
    // clang-format off
    static constexpr DeleteCase kObligations[] = {
        // available 0, sharesTotal 0
        {.vault = {}, .expected = tesSUCCESS},
        {.vault = {.sharesTotal = 1}, .expected = tecHAS_OBLIGATIONS},
        {.vault = {.sharesTotal = 2}, .expected = tecHAS_OBLIGATIONS},
        {.vault = {.available = 1, .sharesTotal = 1}, .expected = tecHAS_OBLIGATIONS},
        {.vault = {.available = 1, .sharesTotal = 2}, .expected = tecHAS_OBLIGATIONS},
        {.vault = {.available = 2, .sharesTotal = 1}, .expected = tecHAS_OBLIGATIONS},
        {.vault = {.available = 2, .sharesTotal = 2}, .expected = tecHAS_OBLIGATIONS},
        // available 0, deployed > 0
        {.vault = {.deployed = 1, .sharesTotal = 1}, .expected = tecHAS_OBLIGATIONS},
        {.vault = {.deployed = 1, .sharesTotal = 2}, .expected = tecHAS_OBLIGATIONS},
        {.vault = {.deployed = 2, .sharesTotal = 1}, .expected = tecHAS_OBLIGATIONS},
    };
    // clang-format on

    // Runs every list on the vaults staged open-ended or, when `closed`, closed-ended in
    // Subscription (VaultDelete has no phase logic).
    void
    runDeleteBoundaries(jtx::Env& env, Setup const& s, bool closed)
    {
        std::uint32_t const p = parentCloseTime(env);
        auto const run = [&](std::string const& name,
                             TestVaults const& vaults,
                             std::span<DeleteCase const> cases) {
            for (Keylet const& vault : vaults)
            {
                beginCase(("delete " + vaultName(env, vault) + " " + name +
                           (closed ? ", closed-ended" : ""))
                              .c_str());
                for (auto const& [row, expected] : cases)
                {
                    StagedVault staged = row;
                    if (closed)
                    {
                        staged.subscriptionDate = p + 1'000;
                        staged.redemptionDate = p + 1'001'000;
                    }
                    AppliedVaultDelete const cpp =
                        applyDelete(env, vault, s.owner, stagedAmounts(env, vault, staged));
                    expectSame(
                        *this, sampleText(staged), cpp, leanCanVaultDelete(cpp.pre), expected);
                }
            }
        };

        run("obligations", s.all, kObligations);
    }

    void
    testDeleteBoundaries(jtx::Env& env, Setup const& s)
    {
        runDeleteBoundaries(env, s, false);
    }

    void
    testClosedEndedDeleteBoundaries(jtx::Env& env, Setup const& s)
    {
        runDeleteBoundaries(env, s, true);
    }

    void
    runTests() override
    {
        jtx::Env env{*this, vaultTestAmendments()};
        Setup const s = setup(env);

        runVaultDelete(env, s.xrpVault, s.owner, 0, 0, 0, tesSUCCESS);
        runVaultDelete(env, s.xrpVault, s.owner, 0, 0, 5, tecHAS_OBLIGATIONS);
        runVaultDelete(env, s.xrpVault, s.owner, 0, 5, 5, tecHAS_OBLIGATIONS);
        runVaultDelete(env, s.xrpVault, s.owner, 5, 5, 5, tecHAS_OBLIGATIONS);
        testDeleteBoundaries(env, s);

        testDeleteInInvestment();
        testClosedEndedDeleteBoundaries(env, s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDelete, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
