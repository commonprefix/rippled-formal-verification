#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultDeleteFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/CreateSetSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/mpt.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/tx/apply.h>

#include <cstdint>
#include <string>
#include <vector>

namespace xrpl::test::formal_verification {

class LeanVaultDelete_test : public LeanSuite
{
    // VaultDelete on `staged`, applied on a throwaway copy of the open ledger, and the model on the
    // same pre-state; returns the C++ verdict.
    TER
    checkDelete(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& owner,
        StagedVault const& staged)
    {
        // Not applyStaged: a deleted vault has no post-state to read.
        OpenView view{*env.current()};
        stageVault(view, vault, owner, staged);
        Vault const pre = readVaultState(view, vault, view.read(vault)->at(sfAsset));
        auto const jt = env.jt(jtx::Vault::del({.owner = owner, .id = vault.key}));
        TER const cppTer = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
        auto const lean = leanCanVaultDelete(pre);
        expectLawful(lean);
        BEAST_EXPECTS(
            lean.ter == cppTer,
            "total " + to_string(pre.assetsTotal) + " shares " + to_string(pre.sharesTotal) +
                ": lean=" + transToken(lean.ter) + " cpp=" + transToken(cppTer));
        return cppTer;
    }

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
            .available = gridUnits(env, xrpVault, available),
            .deployed = gridUnits(env, xrpVault, total - available),
            .sharesTotal = static_cast<std::uint64_t>(shares)};
        TER const cppTer = checkDelete(env, xrpVault, owner, staged);
        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
    }

    void
    testObligationsSweep(
        jtx::Env& env,
        jtx::Account const& owner,
        std::vector<Keylet> const& vaults)
    {
        for (Keylet const& vault : vaults)
        {
            sweepObligations(env, vault, owner);
        }
    }

    // A vault with assets or shares left is tecHAS_OBLIGATIONS; the row is the empty vault.
    void
    sweepObligations(jtx::Env& env, Keylet const& vault, jtx::Account const& owner)
    {
        beginCase(("delete " + vaultName(env, vault) + " obligations-Sweep").c_str());
        runAroundCusp(kDeleteCases, [&](DeleteCusp const& c) {
            StagedVault const staged{
                .available = gridUnits(env, vault, c.available),
                .sharesTotal = static_cast<std::uint64_t>(c.sharesTotal)};
            return checkDelete(env, vault, owner, staged);
        });
    }

    void
    runTests() override
    {
        using namespace jtx;
        // One ledger holding a vault per asset; every staged delete runs on a throwaway view.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        env.close();
        Asset const iou = issuer["USD"].asset();
        Keylet const xrpVault = create_set_sweep::createVaultAt(env, owner, xrpIssue());
        std::vector<Keylet> const all{
            xrpVault,
            create_set_sweep::createVaultAt(env, owner, mptt.issuanceID()),
            create_set_sweep::createVaultAt(env, owner, iou, 0),
            create_set_sweep::createVaultAt(env, owner, iou, 6),
            create_set_sweep::createVaultAt(env, owner, iou, 10)};

        // Covered by testObligationsSweep.
        runVaultDelete(env, xrpVault, owner, 0, 0, 0, tesSUCCESS);
        runVaultDelete(env, xrpVault, owner, 0, 0, 5, tecHAS_OBLIGATIONS);
        runVaultDelete(env, xrpVault, owner, 0, 5, 5, tecHAS_OBLIGATIONS);
        runVaultDelete(env, xrpVault, owner, 5, 5, 5, tecHAS_OBLIGATIONS);

        testObligationsSweep(env, owner, all);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDelete, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
