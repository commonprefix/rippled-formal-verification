#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/formal_verification/tx/lending/LoanSetSweepCases.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/ter.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <exception>
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

    std::optional<SweepLedger> iou_;
    std::optional<SweepLedger> mpt_;

    // A throwaway view of the shared ledger with `s` staged (the vault always in its investment
    // phase).
    bool
    stagedView(SweepLedger& l, OpenView& view, LendingStage s, std::string const& at)
    {
        auto const phase = investment(view);
        s.subscriptionDate = phase.subscriptionDate;
        s.redemptionDate = phase.redemptionDate;
        return tryStage(*this, at, [&] { stageLending(*l.env, view, l.f, s); });
    }

    // Model of LoanBrokerSet creating a broker on `view`: canCreate is preclaim, create is
    // doApply. A preflight rejection (tem) is matched by create rejecting the fields as not
    // lawful. Returns the C++ verdict.
    TER
    checkCreate(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        BrokerConfig const& config,
        std::optional<TER> expected,
        std::string const& at)
    {
        using namespace jtx;
        std::uint8_t const nt = NumericTypeFFI::tagOf(f.asset.raw());
        Vault const pool = readVaultState(view, f.vaultKeylet, f.asset.raw());
        LoanBrokerSetArgs const args{
            .debtMaximum = config.debtMaximum,
            .managementFeeRate = config.managementFeeRate,
            .coverRateMinimum = config.coverRateMinimum,
            .coverRateLiquidation = config.coverRateLiquidation};
        LawfulTerResult const canCreate = leanCanLoanBrokerCreate(pool, config.debtMaximum, nt);
        LeanBrokerResult const created = leanLoanBrokerCreate(args, nt);

        auto const brokerKeylet = keylet::loanBroker(
            f.owner.id(),
            SeqProxy::rawSequence(view.read(keylet::account(f.owner.id()))->at(sfSequence)));
        auto tx = loan_broker::set(f.owner, f.vaultKeylet.key);
        if (config.debtMaximum)
            tx[sfDebtMaximum] = *config.debtMaximum;
        if (config.managementFeeRate)
            tx[sfManagementFeeRate] = *config.managementFeeRate;
        if (config.coverRateMinimum)
            tx[sfCoverRateMinimum] = *config.coverRateMinimum;
        if (config.coverRateLiquidation)
            tx[sfCoverRateLiquidation] = *config.coverRateLiquidation;
        TER const cppTer = applyOn(env, view, tx);

        if (expected)
        {
            BEAST_EXPECTS(
                cppTer == *expected,
                at + ": cpp=" + transToken(cppTer) + " expected " + transToken(*expected));
        }
        BEAST_EXPECTS(!canCreate.leanError.has_value(), at + ": lean canCreate error");
        if (isTemMalformed(cppTer))
        {
            BEAST_EXPECTS(
                created.leanError == LeanError::notLawful,
                at + ": preflight rejects the fields but the model creates the broker");
            return cppTer;
        }
        BEAST_EXPECTS(
            canCreate.ter == cppTer,
            at + ": lean=" + transToken(canCreate.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return cppTer;

        BEAST_EXPECTS(!created.leanError.has_value(), at + ": lean create error");
        expectBrokerMatches(*this, created.broker, readBroker(view, brokerKeylet, f.asset.raw()));
        return cppTer;
    }

    // Model of LoanBrokerSet creating a broker, on the shared IOU ledger (a second broker of its
    // vault); `openEnded` needs its own ledger.
    void
    runCreate(std::string const& label, BrokerConfig const& config, bool openEnded, TER expected)
    {
        using namespace jtx;
        testcase(label);
        if (openEnded)
        {
            Env env(*this);
            auto const f = setUpBrokerVault(env, std::nullopt, Number{10'000}, openEnded, false);
            OpenView view{*env.current()};
            checkCreate(env, f, view, config, expected, label);
            return;
        }
        SweepLedger& l = *iou_;
        OpenView view{*l.env->current()};
        if (stagedView(l, view, {}, label))
            checkCreate(*l.env, l.f, view, config, expected, label);
    }

    // Model of LoanBrokerSet updating the debt maximum of the broker on `view` to `cap`.
    TER
    checkUpdate(
        jtx::Env& env,
        BrokerFixture const& f,
        OpenView& view,
        std::optional<Number> const& cap,
        std::optional<TER> expected,
        std::string const& at)
    {
        using namespace jtx;
        LoanBroker const broker = readBroker(view, f);
        Vault const pool = readVaultState(view, f.vaultKeylet, f.asset.raw());
        LawfulTerResult const canUpdate = leanCanLoanBrokerUpdate(broker, pool, cap);
        expectLawful(canUpdate);
        LeanBrokerResult const updated = leanLoanBrokerUpdate(broker, cap);

        auto tx = loan_broker::set(f.owner, f.vaultKeylet.key);
        tx[sfLoanBrokerID] = to_string(f.brokerKeylet.key);
        if (cap)
            tx[sfDebtMaximum] = *cap;
        TER const cppTer = applyOn(env, view, tx);

        if (expected)
        {
            BEAST_EXPECTS(
                cppTer == *expected,
                at + ": cpp=" + transToken(cppTer) + " expected " + transToken(*expected));
        }
        BEAST_EXPECTS(!canUpdate.leanError.has_value(), at + ": lean canUpdate error");
        if (isTemMalformed(cppTer))
        {
            BEAST_EXPECTS(
                updated.leanError == LeanError::notLawful,
                at + ": preflight rejects the update but the model updates the broker");
            return cppTer;
        }
        BEAST_EXPECTS(
            canUpdate.ter == cppTer,
            at + ": lean=" + transToken(canUpdate.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return cppTer;
        BEAST_EXPECTS(!updated.leanError.has_value(), at + ": lean update error");
        expectBrokerMatches(*this, updated.broker, readBroker(view, f));
        return cppTer;
    }

    // Model of LoanBrokerSet updating the debt maximum, staged on the shared IOU ledger: a broker
    // with a debt maximum of 5000 and, with `withLoan`, a loan of 1000 (so its debt is non-zero).
    void
    runUpdate(
        std::string const& label,
        std::optional<Number> const& debtMaximum,
        bool withLoan,
        TER expected,
        bool equalToDebt = false)
    {
        testcase(label);
        SweepLedger& l = *iou_;
        OpenView view{*l.env->current()};
        LendingStage s{
            .managementFeeRate = 1'000,
            .coverRate = 10'000,
            .debtMaximum = 5'000'000'000,
        };
        if (withLoan)
        {
            s.debt = 1'000'000'000;
            s.cover = 200'000'000;
        }
        if (!stagedView(l, view, s, label))
            return;
        std::optional<Number> const cap =
            equalToDebt ? std::optional<Number>{readBroker(view, l.f).debtTotal} : debtMaximum;
        checkUpdate(*l.env, l.f, view, cap, expected, label);
    }

    // ---- Sweeps ---------------------------------------------------------------------------------

    void
    testDebtMaximumGridSweep()
    {
        sweepDebtMaximumGrid(*iou_);
        sweepDebtMaximumGrid(*mpt_);
    }

    // A debt maximum off the vault grid is tecPRECISION_LOSS, on create and on update. A moved
    // one-step mantissa (gridStep) leaves the grid.
    void
    sweepDebtMaximumGrid(SweepLedger& l)
    {
        for (int const level : loan_set_sweep::kBrokerGridLevels)
        {
            beginCase(("LoanBrokerSet " + assetName(l.f) + " debt maximum grid at 1e" +
                       std::to_string(level) + "-Sweep")
                          .c_str());
            for (auto const& [cusp, cases] : loan_set_sweep::kOneStepCases)
            {
                std::set<TER> seen;
                for (std::int64_t const mantissa : cases)
                {
                    seen.insert(
                        checkStagedCreate(l, gridStep(*l.env->current(), l.f, mantissa, level)));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
            beginCase(("LoanBrokerSet " + assetName(l.f) + " debt maximum update grid at 1e" +
                       std::to_string(level) + "-Sweep")
                          .c_str());
            for (auto const& [cusp, cases] : loan_set_sweep::kOneStepCases)
            {
                std::set<TER> seen;
                for (std::int64_t const mantissa : cases)
                {
                    seen.insert(checkStagedUpdate(
                        l, {}, gridStep(*l.env->current(), l.f, mantissa, level)));
                }
                expectCrossed(cusp, seen, {tecPRECISION_LOSS});
            }
        }
    }

    TER
    checkStagedUpdate(SweepLedger& l, LendingStage const& s, Number const& debtMaximum)
    {
        std::string const at = "update to debt maximum " + to_string(debtMaximum);
        OpenView view{*l.env->current()};
        if (!stagedView(l, view, s, at))
            return tefINTERNAL;
        return checkUpdate(*l.env, l.f, view, debtMaximum, std::nullopt, at);
    }

    // A debt maximum that a 16-digit IOU mantissa cannot hold is tecPRECISION_LOSS: 1e16 units
    // is exact, one unit more is not.
    void
    testDebtMaximumDigitsSweep()
    {
        SweepLedger& l = *iou_;
        beginCase(("LoanBrokerSet " + assetName(l.f) + " debt maximum digits-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kSixteenDigitCases)
        {
            std::set<TER> seen;
            for (std::int64_t const mantissa : cases)
            {
                seen.insert(checkStagedCreate(l, Number{mantissa, -6}));
            }
            expectCrossed(cusp, seen, {tecPRECISION_LOSS});
        }
    }

    void
    testDebtMaximumCapSweep()
    {
        sweepDebtMaximumCap(*iou_);
        sweepDebtMaximumCap(*mpt_);
    }

    // A debt maximum above 2^63 - 1 is temINVALID (preflight; the model rejects the broker as
    // not lawful). The row is the largest 16-digit mantissa at exponent 3 under the cap.
    void
    sweepDebtMaximumCap(SweepLedger& l)
    {
        beginCase(("LoanBrokerSet " + assetName(l.f) + " debt maximum cap-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kDebtCapCases)
        {
            std::set<TER> seen;
            for (std::int64_t const mantissa : cases)
            {
                seen.insert(checkStagedCreate(l, Number{mantissa, 3}));
            }
            expectCrossed(cusp, seen, {temINVALID});
        }
    }

    TER
    checkStagedCreate(SweepLedger& l, Number const& debtMaximum)
    {
        return checkStagedCreate(
            l,
            BrokerConfig{
                .debtMaximum = debtMaximum,
                .managementFeeRate = std::nullopt,
                .coverRateMinimum = std::nullopt,
                .coverRateLiquidation = std::nullopt,
            });
    }

    TER
    checkStagedCreate(SweepLedger& l, BrokerConfig const& config)
    {
        std::string const at = "create with debt maximum " +
            (config.debtMaximum ? to_string(*config.debtMaximum) : std::string{"none"}) + ", fee " +
            std::to_string(config.managementFeeRate.value_or(0)) + ", rates " +
            std::to_string(config.coverRateMinimum.value_or(0)) + "/" +
            std::to_string(config.coverRateLiquidation.value_or(0));
        OpenView view{*l.env->current()};
        if (!stagedView(l, view, {}, at))
            return tefINTERNAL;
        return checkCreate(*l.env, l.f, view, config, std::nullopt, at);
    }

    // A negative debt maximum is temINVALID (the model rejects the broker as not lawful); zero
    // means no maximum. Swept on create and on update.
    void
    testDebtMaximumZeroSweep()
    {
        for (SweepLedger* l : {&*iou_, &*mpt_})
        {
            beginCase(("LoanBrokerSet " + assetName(l->f) + " debt maximum zero-Sweep").c_str());
            for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
            {
                std::set<TER> seen;
                for (std::int64_t const maximum : cases)
                {
                    seen.insert(checkStagedCreate(*l, units(l->f, maximum)));
                }
                expectCrossed(cusp, seen, {temINVALID});
            }
            beginCase(
                ("LoanBrokerSet " + assetName(l->f) + " debt maximum update zero-Sweep").c_str());
            for (auto const& [cusp, cases] : loan_set_sweep::kZeroCases)
            {
                std::set<TER> seen;
                for (std::int64_t const maximum : cases)
                {
                    seen.insert(checkStagedUpdate(*l, {}, units(l->f, maximum)));
                }
                expectCrossed(cusp, seen, {temINVALID});
            }
        }
    }

    // A management fee above 10% or a cover rate above 100% is temINVALID. The cover rates are
    // swept one at a time with the other at the cap (both must be set together).
    void
    testRateCapSweep()
    {
        SweepLedger& l = *iou_;
        auto const config = [](std::int64_t fee, std::int64_t minimum, std::int64_t liquidation) {
            return BrokerConfig{
                .managementFeeRate = static_cast<std::uint16_t>(fee),
                .coverRateMinimum = static_cast<std::uint32_t>(minimum),
                .coverRateLiquidation = static_cast<std::uint32_t>(liquidation),
            };
        };
        auto constexpr cap = loan_set_sweep::kRateScale;
        beginCase(("LoanBrokerSet " + assetName(l.f) + " management fee cap-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kManagementFeeCapCases)
        {
            std::set<TER> seen;
            for (std::int64_t const fee : cases)
            {
                seen.insert(checkStagedCreate(l, config(fee, cap, cap)));
            }
            expectCrossed(cusp, seen, {temINVALID});
        }
        beginCase(("LoanBrokerSet " + assetName(l.f) + " minimum cover rate cap-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kCoverRateCapCases)
        {
            std::set<TER> seen;
            for (std::int64_t const rate : cases)
            {
                seen.insert(checkStagedCreate(l, config(0, rate, cap)));
            }
            expectCrossed(cusp, seen, {temINVALID});
        }
        beginCase(
            ("LoanBrokerSet " + assetName(l.f) + " liquidation cover rate cap-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kCoverRateCapCases)
        {
            std::set<TER> seen;
            for (std::int64_t const rate : cases)
            {
                seen.insert(checkStagedCreate(l, config(0, cap, rate)));
            }
            expectCrossed(cusp, seen, {temINVALID});
        }
    }

    void
    testDebtUpdateSweep()
    {
        sweepDebtUpdate(*iou_);
        sweepDebtUpdate(*mpt_);
    }

    // Lowering the debt maximum below the broker's debt is tecLIMIT_EXCEEDED (zero means no
    // maximum). Rows set it to exactly the debt.
    void
    sweepDebtUpdate(SweepLedger& l)
    {
        beginCase(("LoanBrokerSet " + assetName(l.f) + " debt maximum update-Sweep").c_str());
        for (auto const& [cusp, cases] : loan_set_sweep::kDebtUpdateCases)
        {
            std::set<TER> seen;
            for (loan_set_sweep::DebtUpdateCusp const& c : cases)
            {
                seen.insert(checkStagedUpdate(l, {.debt = c.debt}, units(l.f, c.maximum)));
            }
            expectCrossed(cusp, seen, {tecLIMIT_EXCEEDED});
        }
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

        LoanBroker const broker = readBroker(*env.current(), f.brokerKeylet, f.asset.raw());
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
        jtx::Env iouEnv(*this);
        iou_ = SweepLedger{
            .env = &iouEnv,
            .f = setUpSweepBroker(iouEnv, LendingAsset::iou, loan_set_sweep::kSeedUnits),
        };
        jtx::Env mptEnv(*this);
        mpt_ = SweepLedger{
            .env = &mptEnv,
            .f = setUpSweepBroker(mptEnv, LendingAsset::mpt, loan_set_sweep::kSeedUnits),
        };

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
            "create a broker with a debt maximum not representable as an amount",
            BrokerConfig{.debtMaximum = Number{12'345'678'901'234'567LL, -10}},
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
        // covered by testDebtUpdateSweep: "debt maximum below the debt", "equal to the debt"
        runUpdate("raise the debt maximum", Number{8'000}, false, tesSUCCESS);
        runUpdate("lift the debt maximum", Number{0}, false, tesSUCCESS);
        runUpdate("update without a debt maximum", std::nullopt, false, tesSUCCESS);
        runUpdate("debt maximum off the vault grid", Number{1, -7}, false, tecPRECISION_LOSS);
        runUpdate(
            "debt maximum not representable as an amount",
            Number{12'345'678'901'234'567LL, -10},
            false,
            tecPRECISION_LOSS);
        runUpdate("debt maximum below the debt", Number{500}, true, tecLIMIT_EXCEEDED);
        runUpdate("debt maximum equal to the debt", std::nullopt, true, tesSUCCESS, true);

        // LoanBrokerDelete
        runDelete("delete an empty broker", Number{0}, false, tesSUCCESS);
        runDelete("delete a broker with cover", Number{123'456'789, -6}, false, tesSUCCESS);
        runDelete("delete a broker with a loan", Number{200}, true, tecHAS_OBLIGATIONS);

        // Sweeps
        testDebtMaximumGridSweep();
        testDebtMaximumDigitsSweep();
        testDebtMaximumCapSweep();
        testDebtUpdateSweep();
        testDebtMaximumZeroSweep();
        testRateCapSweep();
    }
};

BEAST_DEFINE_TESTSUITE(LeanLoanBroker, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
