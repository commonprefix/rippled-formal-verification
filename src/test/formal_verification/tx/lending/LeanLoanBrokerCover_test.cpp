#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

// Differential tests of the broker cover transactions: LoanBrokerCoverDeposit, CoverWithdraw and
// CoverClawback. Each compares preclaim (the `can*` TER), doApply (the TER and the broker's
// post-state) and the amount moved.
class LeanLoanBrokerCover_test : public LeanSuite
{
    enum class Op : std::uint8_t { deposit, withdraw, clawback };

    static std::string
    opName(Op op)
    {
        switch (op)
        {
            case Op::deposit:
                return "cover deposit";
            case Op::withdraw:
                return "cover withdraw";
            case Op::clawback:
                return "cover clawback";
        }
        return "?";
    }

    void
    expectTer(TER lean, TER cpp, TER expected, char const* what)
    {
        BEAST_EXPECTS(
            cpp == expected,
            std::string(what) + " cpp=" + transToken(cpp) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            lean == expected,
            std::string(what) + " lean=" + transToken(lean) + " expected " + transToken(expected));
    }

    // Run one cover transaction. `amount` is the transaction amount; for a clawback `nullopt`
    // omits sfAmount (claw everything above the minimum cover). `expectedMoved` is the cover
    // movement both sides must agree on.
    void
    compareCover(
        jtx::Env& env,
        BrokerFixture const& f,
        Op op,
        std::optional<Number> const& amount,
        TER expected,
        std::optional<Number> const& expectedMoved = std::nullopt)
    {
        using namespace jtx;
        LoanBroker const before = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        std::optional<STAmount> const stAmount =
            amount ? std::optional<STAmount>{f.asset(*amount)} : std::nullopt;

        // The model's doApply assumes preclaim passed (a failed precondition there is
        // tecINTERNAL), so it is only run when the model's preclaim accepts.
        LawfulTerResult can{};
        std::optional<LeanCoverResult> result;
        switch (op)
        {
            case Op::deposit:
                can = leanCanCoverDeposit(before, pool, *stAmount);
                if (can.ter == tesSUCCESS)
                    result = leanCoverDeposit(before, pool, *stAmount);
                break;
            case Op::withdraw:
                can = leanCanCoverWithdraw(before, pool, *stAmount);
                if (can.ter == tesSUCCESS)
                    result = leanCoverWithdraw(before, pool, *stAmount);
                break;
            case Op::clawback:
                can = leanCanCoverClawback(before, pool, stAmount);
                if (can.ter == tesSUCCESS)
                    result = leanCoverClawback(before, pool, stAmount);
                break;
        }
        expectLawful(can);

        switch (op)
        {
            case Op::deposit:
                env(loan_broker::coverDeposit(f.owner, f.brokerKeylet.key, *stAmount),
                    jtx::Ter(std::ignore));
                break;
            case Op::withdraw:
                env(loan_broker::coverWithdraw(f.owner, f.brokerKeylet.key, *stAmount),
                    jtx::Ter(std::ignore));
                break;
            case Op::clawback: {
                auto tx = loan_broker::coverClawback(f.issuer);
                tx[sfLoanBrokerID] = to_string(f.brokerKeylet.key);
                if (stAmount)
                    tx[sfAmount] = stAmount->getJson(JsonOptions::Values::None);
                env(tx, jtx::Ter(std::ignore));
                break;
            }
        }
        TER const cppTer = env.ter();
        // Read before closing: a close discards state staged on the open ledger.
        LoanBroker const cpp = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(!can.leanError.has_value(), "lean preclaim error");
        expectTer(can.ter, cppTer, expected, "preclaim");
        if (cppTer != tesSUCCESS || !result)
            return;
        BEAST_EXPECTS(!result->leanError.has_value(), "lean apply error");
        expectTer(result->error.value_or(tesSUCCESS), cppTer, expected, "apply");
        if (result->leanError || result->error)
            return;

        BEAST_EXPECTS(
            result->broker.coverAvailable == cpp.coverAvailable,
            "coverAvailable lean=" + to_string(result->broker.coverAvailable) +
                " cpp=" + to_string(cpp.coverAvailable));
        BEAST_EXPECTS(
            result->broker.debtTotal == cpp.debtTotal && result->broker.loanCount == cpp.loanCount,
            "debt or loan count changed");
        Number const cppMoved = op == Op::deposit ? cpp.coverAvailable - before.coverAvailable
                                                  : before.coverAvailable - cpp.coverAvailable;
        BEAST_EXPECTS(
            Number{result->amount} == cppMoved,
            "moved lean=" + to_string(Number{result->amount}) + " cpp=" + to_string(cppMoved));
        if (expectedMoved)
        {
            BEAST_EXPECTS(
                cppMoved == *expectedMoved,
                "moved " + to_string(cppMoved) + " expected " + to_string(*expectedMoved));
        }
    }

    // A broker with `cover` deposited and, with `withLoan`, a loan of 1000 (minimum cover 100 at
    // the fixture's 10% rate).
    void
    runCover(
        std::string const& label,
        Op op,
        Number const& cover,
        bool withLoan,
        std::optional<Number> const& amount,
        TER expected,
        std::optional<Number> const& expectedMoved = std::nullopt)
    {
        using namespace jtx;
        testcase(opName(op) + ": " + label);

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        if (cover != Number{0})
            depositCover(env, f, cover);
        if (withLoan)
            issueLoan(env, f, Number{1'000});
        compareCover(env, f, op, amount, expected, expectedMoved);
    }

    void
    runTests() override
    {
        // The IOU vault has scale 6, so the cover grid is 1e-6 and the open limit 9e9.
        Number const grid{1, -6};
        Number const openLimit{kOpenLimitUnits, -6};

        // Deposits
        runCover(
            "first deposit", Op::deposit, Number{0}, false, Number{100}, tesSUCCESS, Number{100});
        runCover(
            "second deposit", Op::deposit, Number{100}, false, Number{50}, tesSUCCESS, Number{50});
        runCover(
            "off-grid amount is truncated",
            Op::deposit,
            Number{100},
            false,
            Number{1'234'567, -7},
            tesSUCCESS,
            Number{123'456, -6});
        runCover(
            "sub-grid dust", Op::deposit, Number{100}, false, Number{1, -7}, tecPRECISION_LOSS);
        runCover(
            "up to the open limit",
            Op::deposit,
            Number{0},
            false,
            openLimit,
            tesSUCCESS,
            openLimit);
        runCover(
            "17-digit cover leaves the base exponent",
            Op::deposit,
            Number{0},
            false,
            Number{1, 10},
            tecLIMIT_EXCEEDED);
        runCover(
            "past the open limit",
            Op::deposit,
            Number{0},
            false,
            openLimit + grid,
            tecLIMIT_EXCEEDED);

        // Withdrawals
        runCover("partial", Op::withdraw, Number{100}, false, Number{40}, tesSUCCESS, Number{40});
        runCover(
            "everything", Op::withdraw, Number{100}, false, Number{100}, tesSUCCESS, Number{100});
        runCover(
            "more than available",
            Op::withdraw,
            Number{100},
            false,
            Number{101},
            tecINSUFFICIENT_FUNDS);
        runCover(
            "sub-grid dust", Op::withdraw, Number{100}, false, Number{1, -7}, tecPRECISION_LOSS);
        runCover(
            "down to the minimum cover",
            Op::withdraw,
            Number{200},
            true,
            Number{100},
            tesSUCCESS,
            Number{100});
        runCover(
            "below the minimum cover",
            Op::withdraw,
            Number{200},
            true,
            Number{150},
            tecINSUFFICIENT_FUNDS);

        // Clawbacks by the issuer
        runCover(
            "no amount claws everything",
            Op::clawback,
            Number{100},
            false,
            std::nullopt,
            tesSUCCESS,
            Number{100});
        runCover(
            "zero amount claws everything",
            Op::clawback,
            Number{100},
            false,
            Number{0},
            tesSUCCESS,
            Number{100});
        runCover("partial", Op::clawback, Number{100}, false, Number{40}, tesSUCCESS, Number{40});
        runCover(
            "above the excess is clamped",
            Op::clawback,
            Number{100},
            false,
            Number{150},
            tesSUCCESS,
            Number{100});
        runCover(
            "only the excess over the minimum cover",
            Op::clawback,
            Number{200},
            true,
            std::nullopt,
            tesSUCCESS,
            Number{100});
        runCover(
            "clamped to the excess over the minimum cover",
            Op::clawback,
            Number{200},
            true,
            Number{150},
            tesSUCCESS,
            Number{100});
        runCover(
            "no excess cover", Op::clawback, Number{0}, false, std::nullopt, tecINSUFFICIENT_FUNDS);
        runCover(
            "sub-grid dust", Op::clawback, Number{100}, false, Number{1, -7}, tecPRECISION_LOSS);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanBrokerCover, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
