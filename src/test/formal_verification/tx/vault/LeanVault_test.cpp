#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>

#include <xrpl/basics/Number.h>

#include <optional>
#include <string>

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

    void
    runLawful(Vault const& s, bool shouldBeLawful, std::string const& label)
    {
        testcase(label);
        BEAST_EXPECTS(VaultFFI::build(s).has_value() == shouldBeLawful, label);
    }

    void
    testLawful()
    {
        runLawful(baseline(), true, "valid baseline");
        {
            auto s = baseline();
            s.assetsDeployed = Number{3};
            s.assetsReserved = Number{2};
            s.lossUnrealized = Number{3};
            s.yieldUnrealized = Number{1};
            runLawful(s, true, "lent-out vault with loss, reserve and yield");
        }
        runLawful(closedEnded(), true, "closed-ended vault with an early-exit fee");
        {
            auto s = baseline();
            s.ownerCanBlockDeposit = true;
            s.depositBlocked = true;
            runLawful(s, true, "deposits blocked by an owner allowed to");
        }
        // The cap is a transaction check now, not a vault invariant.
        {
            auto s = baseline();
            s.assetsMaximum = Number{3};
            runLawful(s, true, "assetsTotal above assetsMaximum");
        }
    }

    // RawVault.WF clauses (the *_norm clauses are omitted)
    void
    testWellFormed()
    {
        {
            auto s = baseline();
            s.sharesTotal = Number{-5};
            runLawful(s, false, "negative sharesTotal");
        }
        {
            auto s = baseline();
            s.sharesTotal = Number{15, -1};  // 1.5, not an integer
            runLawful(s, false, "fractional sharesTotal");
        }
        {
            auto s = baseline();
            s.numericType = 1;  // int64 (MPT) asset must have scale 0
            s.scale = 3;
            runLawful(s, false, "integral asset with nonzero scale");
        }
        {
            auto s = baseline();
            s.scale = 11;
            runLawful(s, false, "scale above 10");
        }
    }

    // RawVault.Valid clauses.
    void
    testValid()
    {
        {
            auto s = baseline();
            s.assetsAvailable = Number{-1};
            runLawful(s, false, "negative assetsAvailable");
        }
        {
            auto s = baseline();
            s.assetsDeployed = Number{-1};
            runLawful(s, false, "negative assetsDeployed");
        }
        {
            auto s = baseline();
            s.assetsReserved = Number{-1};
            runLawful(s, false, "negative assetsReserved");
        }
        {
            auto s = baseline();
            s.lossUnrealized = Number{-1};
            runLawful(s, false, "negative lossUnrealized");
        }
        {
            auto s = baseline();
            s.yieldUnrealized = Number{-1};
            runLawful(s, false, "negative yieldUnrealized");
        }
        // Total and available are 0 so only assetsMaximum_pos fails.
        {
            auto s = baseline();
            s.assetsAvailable = Number{0};
            s.sharesTotal = Number{0};
            s.assetsMaximum = Number{0};
            runLawful(s, false, "assetsMaximum is zero");
        }
        {
            auto s = baseline();
            s.sharesTotal = Number{0};
            runLawful(s, false, "zero shares with available assets");
        }
        {
            auto s = baseline();
            s.assetsAvailable = Number{0};
            s.assetsDeployed = Number{5};
            s.sharesTotal = Number{0};
            runLawful(s, false, "zero shares with deployed assets");
        }
        {
            auto s = baseline();
            s.assetsDeployed = Number{2};
            s.lossUnrealized = Number{3};
            runLawful(s, false, "lossUnrealized above assetsDeployed");
        }
        {
            auto s = baseline();
            s.assetsDeployed = Number{2};
            s.assetsReserved = Number{3};
            runLawful(s, false, "assetsReserved above assetsDeployed");
        }
        // 17 significant digits do not fit an IOU STAmount.
        {
            auto s = baseline();
            s.assetsDeployed = Number{12'345'678'901'234'567LL};
            runLawful(s, false, "assetsDeployed not representable");
        }
        {
            auto s = baseline();
            s.depositBlocked = true;
            runLawful(s, false, "deposits blocked by an owner not allowed to");
        }
        {
            auto s = closedEnded();
            s.redemptionDate = 1'179;
            runLawful(s, false, "investment period below 180 s");
        }
        {
            auto s = closedEnded();
            s.redemptionDate = 1'000 + 30u * 31'556'952u;
            runLawful(s, false, "investment period of 30 years");
        }
        {
            auto s = closedEnded();
            s.redemptionDate = std::nullopt;
            runLawful(s, false, "subscription date without a redemption date");
        }
        {
            auto s = baseline();
            s.earlyExitFeeRate = 0;
            runLawful(s, false, "early-exit fee on an open-ended vault");
        }
        {
            auto s = closedEnded();
            s.earlyExitFeeRate = 100'001;
            runLawful(s, false, "early-exit fee above 100%");
        }
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
