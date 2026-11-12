// Scratch suite (manual, not part of the formal_verification group): reproductions of the model/C++
// gaps in ffi-model-gaps.md. Run with --unittest=LeanCuspScratch. Each check prints
// "cpp=... lean=..."; a failure is a disagreement.

#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultCreateFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/tx/apply.h>

#include <cstdint>
#include <limits>
#include <optional>
#include <string>
#include <tuple>

namespace xrpl::test::formal_verification {

class LeanCuspScratch_test : public LeanSuite
{
    static std::string
    leanText(std::optional<LeanError> const& error, std::optional<TER> const& ter)
    {
        if (error)
            return "model error " + std::to_string(static_cast<int>(*error));
        return transToken(ter.value_or(tesSUCCESS));
    }

    // Report both verdicts and expect them to agree (a model error counts as tefEXCEPTION).
    void
    report(
        std::string const& label,
        TER cpp,
        std::optional<LeanError> const& leanError,
        std::optional<TER> const& leanTer)
    {
        TER const lean = leanError ? TER{tefEXCEPTION} : leanTer.value_or(tesSUCCESS);
        log << "SCRATCH " << label << ": cpp=" << transToken(cpp)
            << " lean=" << leanText(leanError, leanTer) << std::endl;
        BEAST_EXPECTS(
            lean == cpp,
            label + ": cpp=" + transToken(cpp) + " lean=" + leanText(leanError, leanTer));
    }

    // Gap 16: an XRP withdraw by shares whose payout converts to more than 1e17 drops.
    void
    gapWithdrawSharesOutOfRange(std::int64_t shares)
    {
        using namespace jtx;
        testcase("gap: XRP withdraw by " + std::to_string(shares) + " shares");
        Env env(*this);
        Account const owner{"owner"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, holder);
        env.close();
        Keylet const vault = createVault(env, owner, xrpIssue());
        env(jtx::Vault::deposit({.depositor = holder, .id = vault.key, .amount = XRP(1)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        Vault const before = readVaultState(env, vault, xrpIssue());
        STAmount const amount{MPTIssue{env.le(vault)->at(sfShareMPTID)}, shares};
        LeanVaultResult const lean = leanVaultWithdraw(
            before,
            amount,
            true,
            parentCloseTime(env),
            holderOwnsAllShares(env, vault, holder),
            Number{fetchHolderShares(env, vault, holder)});
        env(jtx::Vault::withdraw({.depositor = holder, .id = vault.key, .amount = amount}),
            jtx::Ter(std::ignore));
        report(
            "withdraw " + std::to_string(shares) + " shares of 1e6 (NAV 1e6 drops)",
            env.ter(),
            lean.leanError,
            lean.error);
    }

    // Gap 1: clawing back more than one of two holders' shares are worth.
    void
    gapClawbackOverHolderValue(std::int64_t amount)
    {
        using namespace jtx;
        testcase("gap: clawback " + std::to_string(amount) + " from a holder worth 1000");
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const alice{"alice"};
        Account const bob{"bob"};
        env.fund(XRP(1'000'000), owner, issuer, alice, bob);
        env.close();
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();
        PrettyAsset const iou = issuer["USD"];
        env.trust(iou(1'000'000), alice);
        env.trust(iou(1'000'000), bob);
        env(pay(issuer, alice, iou(10'000)));
        env(pay(issuer, bob, iou(10'000)));
        env.close();

        jtx::Vault const v{env};
        auto [tx, vault] = v.create({.owner = owner, .asset = iou.raw()});
        tx[sfScale] = 0;
        env(tx);
        env.close();
        env(jtx::Vault::deposit({.depositor = alice, .id = vault.key, .amount = iou(1'000)}),
            jtx::Ter(tesSUCCESS));
        env(jtx::Vault::deposit({.depositor = bob, .id = vault.key, .amount = iou(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        Vault const before = readVaultState(env, vault, iou.raw());
        STAmount const request = iou(amount);
        LeanVaultResult const lean = leanVaultClawback(
            before,
            request,
            fetchHolderShares(env, vault, alice),
            holderOwnsAllShares(env, vault, alice));
        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vault.key, .holder = alice, .amount = request}),
            jtx::Ter(std::ignore));
        report(
            "claw " + std::to_string(amount) + " from alice (1000 of 2000 shares)",
            env.ter(),
            lean.leanError,
            lean.error);
    }

    // Gap 3: an XRP vault created with an AssetsMaximum above 1e17 drops.
    void
    gapCreateXrpMaximum(Number const& maximum)
    {
        using namespace jtx;
        testcase("gap: create XRP vault with maximum " + to_string(maximum));
        Env env(*this);
        Account const owner{"owner"};
        env.fund(XRP(1'000'000), owner);
        env.close();

        VaultCreateArgs const args{.assetsMaximum = maximum, .numericType = 0};
        LawfulTerResult const can = leanCanVaultCreate(args, parentCloseTime(env));
        LeanCreateResult const created = leanVaultCreate(args);
        jtx::Vault const v{env};
        auto [tx, vault] = v.create({.owner = owner, .asset = xrpIssue()});
        tx[sfAssetsMaximum] = maximum;
        env(tx, jtx::Ter(std::ignore));
        TER const cpp = env.ter();
        std::optional<LeanError> const leanError =
            can.leanError ? can.leanError : created.leanError;
        // The create suite's convention: a preflight rejection must be a not-lawful vault.
        bool const agree =
            isTemMalformed(cpp) ? leanError == LeanError::notLawful : !leanError && can.ter == cpp;
        log << "SCRATCH create XRP maximum " << to_string(maximum) << ": cpp=" << transToken(cpp)
            << " lean canCreate=" << transToken(can.ter) << " create="
            << (created.leanError ? leanText(created.leanError, std::nullopt) : "lawful vault")
            << std::endl;
        BEAST_EXPECTS(
            agree, "create XRP maximum " + to_string(maximum) + ": cpp=" + transToken(cpp));
    }

    void
    runTests() override
    {
        constexpr std::int64_t kInt64Max = std::numeric_limits<std::int64_t>::max();
        // Payout = shares drops here: <= 1e17 is in range, above it STAmount throws.
        gapWithdrawSharesOutOfRange(100'000'000'000'000'000);
        gapWithdrawSharesOutOfRange(100'000'000'000'000'001);
        gapWithdrawSharesOutOfRange(200'000'000'000'000'000);
        gapWithdrawSharesOutOfRange(kInt64Max);

        gapClawbackOverHolderValue(1'000);
        gapClawbackOverHolderValue(1'001);
        gapClawbackOverHolderValue(1'500);

        gapCreateXrpMaximum(Number{100'000'000'000'000'000});
        gapCreateXrpMaximum(Number{100'000'000'000'000'001});
        gapCreateXrpMaximum(Number{200'000'000'000'000'000});
    }
};

BEAST_DEFINE_TESTSUITE_MANUAL(LeanCuspScratch, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
