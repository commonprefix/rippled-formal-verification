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
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test::formal_verification {

// Differential tests of the loan broker's lawful state and of LoanBrokerSet (create and update)
// and LoanBrokerDelete against the model.
class LeanLoanBroker_test : public LeanSuite
{
    // A valid broker: IOU asset, 1% management fee, 10% / 20% cover rates, some cover, no loans.
    static LoanBroker
    baseline()
    {
        return {
            .numericType = 2,
            .managementFeeRate = 1'000,
            .coverRateMinimum = 10'000,
            .coverRateLiquidation = 20'000,
            .debtTotal = Number{0},
            .debtMaximum = Number{0},
            .coverAvailable = Number{100},
            .loanCount = 0};
    }

    void
    runLawful(LoanBroker const& s, bool shouldBeLawful, std::string const& label)
    {
        testcase(label);
        BEAST_EXPECTS(LoanBrokerFFI::build(s).has_value() == shouldBeLawful, label);
    }

    void
    testLawful()
    {
        runLawful(baseline(), true, "valid baseline");
        {
            auto s = baseline();
            s.loanCount = 1;
            s.debtTotal = Number{500};
            s.debtMaximum = Number{1'000};
            runLawful(s, true, "broker with a loan under its cap");
        }
        {
            auto s = baseline();
            s.coverRateMinimum = 0;
            s.coverRateLiquidation = 0;
            runLawful(s, true, "broker without cover rates");
        }
        {
            auto s = baseline();
            s.debtTotal = Number{-1};
            runLawful(s, false, "negative debtTotal");
        }
        {
            auto s = baseline();
            s.coverAvailable = Number{-1};
            runLawful(s, false, "negative coverAvailable");
        }
        {
            auto s = baseline();
            s.loanCount = 1;
            s.debtTotal = Number{500};
            s.debtMaximum = Number{100};
            runLawful(s, false, "debtTotal above debtMaximum");
        }
        {
            auto s = baseline();
            s.debtTotal = Number{500};
            runLawful(s, false, "debt without a loan");
        }
        {
            auto s = baseline();
            s.debtMaximum = Number{-1};
            runLawful(s, false, "negative debtMaximum");
        }
        {
            auto s = baseline();
            s.debtMaximum = Number{1, 19};
            runLawful(s, false, "debtMaximum above 2^63-1");
        }
        {
            auto s = baseline();
            s.managementFeeRate = 10'001;
            runLawful(s, false, "management fee above 10%");
        }
        {
            auto s = baseline();
            s.coverRateMinimum = 100'001;
            runLawful(s, false, "minimum cover rate above 100%");
        }
        {
            auto s = baseline();
            s.coverRateLiquidation = 100'001;
            runLawful(s, false, "liquidation cover rate above 100%");
        }
        {
            auto s = baseline();
            s.coverRateLiquidation = 0;
            runLawful(s, false, "minimum cover rate without a liquidation rate");
        }
        {
            auto s = baseline();
            s.coverRateMinimum = 0;
            runLawful(s, false, "liquidation cover rate without a minimum rate");
        }
    }

    void
    expectSameBroker(LoanBroker const& lean, LoanBroker const& cpp)
    {
        auto const check = [&](char const* name, Number const& l, Number const& c) {
            BEAST_EXPECTS(
                l == c, std::string(name) + " lean=" + to_string(l) + " cpp=" + to_string(c));
        };
        check("debtTotal", lean.debtTotal, cpp.debtTotal);
        check("debtMaximum", lean.debtMaximum, cpp.debtMaximum);
        check("coverAvailable", lean.coverAvailable, cpp.coverAvailable);
        BEAST_EXPECTS(
            lean.loanCount == cpp.loanCount,
            "loanCount lean=" + std::to_string(lean.loanCount) +
                " cpp=" + std::to_string(cpp.loanCount));
        BEAST_EXPECTS(
            lean.managementFeeRate == cpp.managementFeeRate &&
                lean.coverRateMinimum == cpp.coverRateMinimum &&
                lean.coverRateLiquidation == cpp.coverRateLiquidation,
            "rates differ");
    }

    // Model of LoanBrokerSet creating a broker: canCreate is preclaim, create is doApply. A
    // preflight rejection (tem) is matched by create rejecting the fields as not lawful.
    void
    runCreate(std::string const& label, BrokerConfig const& config, bool openEnded, TER expected)
    {
        using namespace jtx;
        testcase(label);

        Env env(*this);
        auto const f = setUpBrokerVault(env, std::nullopt, Number{10'000}, openEnded, false);
        std::uint8_t const nt = NumericTypeFFI::tagOf(f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LoanBrokerSetArgs const args{
            .debtMaximum = config.debtMaximum,
            .managementFeeRate = config.managementFeeRate,
            .coverRateMinimum = config.coverRateMinimum,
            .coverRateLiquidation = config.coverRateLiquidation};
        LawfulTerResult const canCreate = leanCanLoanBrokerCreate(pool, config.debtMaximum, nt);
        LeanBrokerResult const created = leanLoanBrokerCreate(args, nt);

        auto const brokerKeylet =
            keylet::loanBroker(f.owner.id(), SeqProxy::rawSequence(env.seq(f.owner)));
        auto tx = loan_broker::set(f.owner, f.vaultKeylet.key);
        if (config.debtMaximum)
            tx[sfDebtMaximum] = *config.debtMaximum;
        if (config.managementFeeRate)
            tx[sfManagementFeeRate] = *config.managementFeeRate;
        if (config.coverRateMinimum)
            tx[sfCoverRateMinimum] = *config.coverRateMinimum;
        if (config.coverRateLiquidation)
            tx[sfCoverRateLiquidation] = *config.coverRateLiquidation;
        env(tx, jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!canCreate.leanError.has_value(), "lean canCreate error");
        if (isTemMalformed(cppTer))
        {
            BEAST_EXPECTS(
                created.leanError == LeanError::notLawful,
                "preflight rejects the fields but the model creates the broker");
            return;
        }
        BEAST_EXPECTS(
            canCreate.ter == cppTer,
            std::string("lean=") + transToken(canCreate.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return;

        BEAST_EXPECTS(!created.leanError.has_value(), "lean create error");
        expectSameBroker(created.broker, readLoanBrokerState(env, brokerKeylet, f.asset.raw()));
    }

    // Model of LoanBrokerSet updating the debt maximum. With `withLoan` the broker carries a loan
    // of 1000, so its debt is non-zero.
    void
    runUpdate(
        std::string const& label,
        std::optional<Number> const& debtMaximum,
        bool withLoan,
        TER expected,
        bool equalToDebt = false)
    {
        using namespace jtx;
        testcase(label);

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{.debtMaximum = Number{5'000}});
        if (withLoan)
        {
            depositCover(env, f, Number{200});
            issueLoan(env, f, Number{1'000});
        }

        LoanBroker const broker = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        std::optional<Number> const cap =
            equalToDebt ? std::optional<Number>{broker.debtTotal} : debtMaximum;
        LawfulTerResult const canUpdate = leanCanLoanBrokerUpdate(broker, pool, cap);
        expectLawful(canUpdate);
        LeanBrokerResult const updated = leanLoanBrokerUpdate(broker, cap);

        auto tx = loan_broker::set(f.owner, f.vaultKeylet.key);
        tx[sfLoanBrokerID] = to_string(f.brokerKeylet.key);
        if (cap)
            tx[sfDebtMaximum] = *cap;
        env(tx, jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        LoanBroker const cpp = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!canUpdate.leanError.has_value(), "lean canUpdate error");
        BEAST_EXPECTS(
            canUpdate.ter == cppTer,
            std::string("lean=") + transToken(canUpdate.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return;
        BEAST_EXPECTS(!updated.leanError.has_value(), "lean update error");
        expectSameBroker(updated.broker, cpp);
    }

    // Model of LoanBrokerDelete: canDelete is preclaim; the cover returned to the owner is the
    // broker's rounded coverAvailable.
    void
    runDelete(std::string const& label, Number const& cover, bool withLoan, TER expected)
    {
        using namespace jtx;
        testcase(label);

        Env env(*this);
        auto const f = setUpBrokerVault(env, BrokerConfig{});
        if (cover != Number{0})
            depositCover(env, f, cover);
        if (withLoan)
            issueLoan(env, f, Number{1'000});

        LoanBroker const broker = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LawfulTerResult const canDelete = leanCanLoanBrokerDelete(broker, pool);
        expectLawful(canDelete);
        LeanRoundedCoverResult const rounded = leanLoanBrokerRoundedCover(broker);

        Number const ownerBefore = iouBalance(env, f.owner, f.asset);
        env(loan_broker::del(f.owner, f.brokerKeylet.key), jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(!canDelete.leanError.has_value(), "lean canDelete error");
        BEAST_EXPECTS(
            canDelete.ter == cppTer,
            std::string("lean=") + transToken(canDelete.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return;
        BEAST_EXPECT(!env.le(f.brokerKeylet));
        BEAST_EXPECTS(!rounded.leanError.has_value(), "lean roundedCoverAvailable error");
        Number const received = iouBalance(env, f.owner, f.asset) - ownerBefore;
        BEAST_EXPECTS(
            Number{rounded.amount} == received,
            "cover returned lean=" + to_string(Number{rounded.amount}) +
                " cpp=" + to_string(received));
    }

    void
    runTests() override
    {
        testLawful();

        // LoanBrokerSet: create
        runCreate("create a broker on a closed-ended vault", BrokerConfig{}, false, tesSUCCESS);
        runCreate(
            "create a broker with a debt maximum",
            BrokerConfig{.debtMaximum = Number{1'000'000}},
            false,
            tesSUCCESS);
        runCreate(
            "create a broker without cover rates",
            BrokerConfig{.coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt},
            false,
            tesSUCCESS);
        runCreate("create a broker on an open-ended vault", BrokerConfig{}, true, tecNO_PERMISSION);
        runCreate(
            "create a broker with a debt maximum off the vault grid",
            BrokerConfig{.debtMaximum = Number{1, -7}},
            false,
            tecPRECISION_LOSS);
        runCreate(
            "create a broker with a negative debt maximum",
            BrokerConfig{.debtMaximum = Number{-1}},
            false,
            temINVALID);
        runCreate(
            "create a broker with a management fee above 10%",
            BrokerConfig{.managementFeeRate = 10'001},
            false,
            temINVALID);
        runCreate(
            "create a broker with a cover rate above 100%",
            BrokerConfig{.coverRateMinimum = 100'001},
            false,
            temINVALID);
        runCreate(
            "create a broker with a minimum cover rate but no liquidation rate",
            BrokerConfig{.coverRateLiquidation = std::nullopt},
            false,
            temINVALID);

        // LoanBrokerSet: update
        runUpdate("raise the debt maximum", Number{8'000}, false, tesSUCCESS);
        runUpdate("lift the debt maximum", Number{0}, false, tesSUCCESS);
        runUpdate("update without a debt maximum", std::nullopt, false, tesSUCCESS);
        runUpdate("debt maximum off the vault grid", Number{1, -7}, false, tecPRECISION_LOSS);
        runUpdate("debt maximum below the debt", Number{500}, true, tecLIMIT_EXCEEDED);
        runUpdate("debt maximum equal to the debt", std::nullopt, true, tesSUCCESS, true);

        // LoanBrokerDelete
        runDelete("delete an empty broker", Number{0}, false, tesSUCCESS);
        runDelete("delete a broker with cover", Number{123'456'789, -6}, false, tesSUCCESS);
        runDelete("delete a broker with a loan", Number{200}, true, tecHAS_OBLIGATIONS);
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanBroker, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
