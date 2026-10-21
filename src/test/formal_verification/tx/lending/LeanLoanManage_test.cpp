#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

// Differential tests of LoanManage: impair, unimpair and default.
class LeanLoanManage_test : public LeanSuite
{
    static std::uint32_t
    flagsOf(ManageAction action)
    {
        switch (action)
        {
            case ManageAction::impair:
                return tfLoanImpair;
            case ManageAction::unimpair:
                return tfLoanUnimpair;
            case ManageAction::defaultLoan:
                return tfLoanDefault;
        }
        return 0;
    }

    static std::string
    actionName(ManageAction action)
    {
        switch (action)
        {
            case ManageAction::impair:
                return "impair";
            case ManageAction::unimpair:
                return "unimpair";
            case ManageAction::defaultLoan:
                return "default";
        }
        return "?";
    }

    void
    expectTer(TER lean, TER cpp, TER expected)
    {
        BEAST_EXPECTS(
            cpp == expected,
            std::string("cpp=") + transToken(cpp) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            lean == expected,
            std::string("lean=") + transToken(lean) + " expected " + transToken(expected));
    }

    void
    compareManage(
        jtx::Env& env,
        BrokerFixture const& f,
        Keylet const& loanKeylet,
        LoanParams const& p,
        ManageAction action,
        TER expected)
    {
        using namespace jtx;
        Loan const loan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        std::uint32_t const now = parentCloseTime(env);

        LawfulTerResult const can = leanCanLoanManage(loan, action, now);
        expectLawful(can);
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS)
            result = leanLoanManage(loan, pool, action, now);

        env(loan::manage(f.owner, loanKeylet.key, flagsOf(action)), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        Loan const cppLoan = readLoanState(env, loanKeylet, f.asset.raw(), p.paymentTotal);
        Vault const cppPool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!can.leanError.has_value(), "lean canManage error");
        if (result)
            BEAST_EXPECTS(!result->leanError.has_value(), "lean manage error");
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        expectTer(lean, cppTer, expected);
        if (cppTer != tesSUCCESS || !result || result->leanError || result->error)
            return;

        expectLoanMatches(*this, result->loan, cppLoan);
        expectVaultMatches(*this, result->pool, cppPool);
        expectBrokerMatches(*this, result->loan.broker, cppLoan.broker);
        // A default moves the cover it consumes into the vault.
        expectNumber(
            *this,
            "amount to pool",
            result->amountToPool,
            cppPool.assetsAvailable - pool.assetsAvailable);
    }

    // A 1000 loan (two instalments 600 s apart, 60 s grace) on a broker with 500 of cover. The
    // ledger is advanced `delay` seconds past the loan's start, and the loan is impaired first if
    // `impairFirst` (which needs the loan to be late).
    enum class LoanKind : std::uint8_t { active, pending, defaulted, paidOff };

    void
    runManage(
        std::string const& label,
        std::uint32_t delay,
        bool impairFirst,
        ManageAction action,
        TER expected,
        LoanKind kind = LoanKind::active)
    {
        using namespace jtx;
        testcase(actionName(action) + ": " + label);

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        depositCover(env, f, Number{500});
        LoanParams p;
        if (kind == LoanKind::pending)
            p.startDate = parentCloseTime(env) + 1'000;
        if (kind == LoanKind::paidOff)
            p.paymentTotal = 1;
        auto const loanKeylet = submitLoanSet(env, f, p);
        if (kind == LoanKind::paidOff)
        {
            env(loan::pay(f.borrower, loanKeylet.key, f.asset(1'000)), jtx::Ter(tesSUCCESS));
            env.close();
        }
        if (delay != 0)
            closeAt(env, parentCloseTime(env) + delay);
        if (impairFirst)
        {
            env(loan::manage(f.owner, loanKeylet.key, tfLoanImpair), jtx::Ter(tesSUCCESS));
            env.close();
        }
        if (kind == LoanKind::defaulted)
        {
            env(loan::manage(f.owner, loanKeylet.key, tfLoanDefault), jtx::Ter(tesSUCCESS));
            env.close();
        }
        compareManage(env, f, loanKeylet, p, action, expected);
    }

    void
    runTests() override
    {
        // The first instalment is due 600 s after the start, with a 60 s grace period.
        runManage("a late loan", 601, false, ManageAction::impair, tesSUCCESS);
        runManage("a loan that is not late", 0, false, ManageAction::impair, tecTOO_SOON);
        runManage("an impaired loan", 601, true, ManageAction::impair, tecNO_PERMISSION);

        runManage("an impaired loan", 601, true, ManageAction::unimpair, tesSUCCESS);
        runManage(
            "a loan that is not impaired", 0, false, ManageAction::unimpair, tecNO_PERMISSION);

        runManage(
            "before the grace period ends", 601, false, ManageAction::defaultLoan, tecTOO_SOON);
        runManage("after the grace period", 700, false, ManageAction::defaultLoan, tesSUCCESS);
        runManage(
            "an impaired loan after the grace period",
            700,
            true,
            ManageAction::defaultLoan,
            tesSUCCESS);

        // Loans that cannot be managed at all
        runManage(
            "a pending proposal",
            0,
            false,
            ManageAction::impair,
            tecNO_PERMISSION,
            LoanKind::pending);
        runManage(
            "a defaulted loan",
            700,
            false,
            ManageAction::impair,
            tecNO_PERMISSION,
            LoanKind::defaulted);
        runManage(
            "a paid-off loan", 0, false, ManageAction::impair, tecNO_PERMISSION, LoanKind::paidOff);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanManage, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
