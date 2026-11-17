#pragma once

#include <test/formal_verification/ffi/LeanObjectFFI.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/protocol/Asset.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>

#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

// The model accepts the staged state as lawful and agrees with C++ on the verdict and, when both
// succeed, on the vault. Returns the C++ verdict.
inline TER
expectAgree(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedVaultTx const& cpp,
    LeanVaultResult const& lean)
{
    suite.expect(lean.leanError != LeanError::notLawful, at + "model: staged state not lawful");
    TER const leanTer = lean.leanError ? TER{tefEXCEPTION} : lean.error.value_or(tesSUCCESS);
    suite.expect(
        leanTer == cpp.ter, at + "lean=" + transToken(leanTer) + " cpp=" + transToken(cpp.ter));
    if (cpp.ter == tesSUCCESS && leanTer == tesSUCCESS)
        expectSameVault(suite, at, lean.vault, cpp.post);
    return cpp.ter;
}

// A deposit (or donation) on a throwaway view of `staged` and the model on the same state must
// agree, and a deposit never charges more than offered. Returns the C++ verdict.
inline TER
checkDeposit(
    beast::unit_test::Suite& suite,
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& depositor,
    StagedAmounts const& staged,
    STAmount const& amount,
    bool donate = false)
{
    AppliedVaultTx const cpp = applyDeposit(env, vault, depositor, staged, amount, donate);
    LeanVaultResult const lean = leanVaultDeposit(cpp.pre, amount, donate, parentCloseTime(env));
    std::string const at = sampleText(staged, amount);
    if (expectAgree(suite, at, cpp, lean) != tesSUCCESS || lean.leanError || lean.error)
        return cpp.ter;
    Number const charged = cpp.post.assetsTotal - cpp.pre.assetsTotal;
    suite.expect(charged <= Number{amount}, at + "cpp charged " + to_string(charged));
    suite.expect(
        Number{lean.assets} <= Number{amount},
        at + "lean charged " + to_string(Number{lean.assets}));
    return cpp.ter;
}

// A withdrawal (by assets, or by shares when `amount` is in shares) from a staged vault whose
// pseudo-account holds the available assets and whose holder holds `holderShares` (all shares
// when unset). Both sides must agree, also on the payout: what left the vault (an early-exit fee
// stays behind), equal to `expectedPayout` when given.
inline AppliedVaultTx
checkWithdraw(
    beast::unit_test::Suite& suite,
    jtx::Env& env,
    Keylet const& vault,
    jtx::Account const& holder,
    StagedAmounts const& staged,
    STAmount const& amount,
    std::optional<Number> const& expectedPayout = std::nullopt)
{
    bool const byShares = amount.asset() != Asset{env.le(vault)->at(sfAsset)};
    AppliedVaultTx const cpp = applyWithdraw(env, vault, holder, staged, amount);
    LeanVaultResult const lean = leanWithdraw(cpp, staged, amount, byShares, parentCloseTime(env));
    std::string const at = sampleText(staged, amount);
    if (expectAgree(suite, at, cpp, lean) != tesSUCCESS || lean.leanError || lean.error)
        return cpp;
    Number const cppPayout = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;
    suite.expect(
        Number{lean.assets} == cppPayout,
        at + "payout lean=" + to_string(Number{lean.assets}) + " cpp=" + to_string(cppPayout));
    if (expectedPayout)
    {
        suite.expect(
            cppPayout == *expectedPayout,
            at + "payout " + to_string(cppPayout) + " expected " + to_string(*expectedPayout));
    }
    return cpp;
}

}  // namespace xrpl::test::formal_verification
