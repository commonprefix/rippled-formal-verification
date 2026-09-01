#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/LawfulVaultFFI.h>

#include <xrpl/basics/Number.h>

#include <optional>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

// A not-lawful result is the expected and each case violates one invariant clause
// (RawVault.WF / RawVault.Valid) and build must reject it.
class LeanLawfulVault_test : public LeanSuite
{
    // A valid vault: solvent, fractional (IOU) asset at scale 6, no cap, no unrealized loss.
    static LawfulVault
    baseline()
    {
        return {
            .assetsTotal = Number{5},
            .assetsAvailable = Number{5},
            .assetsMaximum = std::nullopt,
            .numericType = 2,
            .scale = 6,
            .sharesTotal = Number{1'000'000},
            .lossUnrealized = Number{0}};
    }

    void
    runLawful(LawfulVault const& s, bool shouldBeLawful, std::string const& label)
    {
        testcase(label);
        BEAST_EXPECTS(LawfulVaultFFI::build(s).has_value() == shouldBeLawful, label);
    }

    void
    testBaseline()
    {
        runLawful(baseline(), true, "valid baseline");
    }

    // RawVault.WF clauses (the five *_norm clauses are omitted)
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
            s.scale = 19;
            runLawful(s, false, "scale above 18");
        }
    }

    // RawVault.Valid clauses.
    void
    testValid()
    {
        // A negative total also breaks the ordering and loss clauses. assetsAvailable is set to 0
        // so only the sign of the total is exercised beyond those.
        {
            auto s = baseline();
            s.assetsTotal = Number{-1};
            s.assetsAvailable = Number{0};
            runLawful(s, false, "negative assetsTotal");
        }
        {
            auto s = baseline();
            s.assetsAvailable = Number{-1};
            runLawful(s, false, "negative assetsAvailable");
        }
        // available > total forces the loss gap negative, so this also breaks lossUnrealized_le.
        {
            auto s = baseline();
            s.assetsAvailable = Number{10};
            runLawful(s, false, "assetsAvailable exceeds assetsTotal");
        }
        // Zero cap. Total and available are 0 so only assetsMaximum_pos fails.
        {
            auto s = baseline();
            s.assetsTotal = Number{0};
            s.assetsAvailable = Number{0};
            s.assetsMaximum = Number{0};
            runLawful(s, false, "assetsMaximum is zero");
        }
        {
            auto s = baseline();
            s.sharesTotal = Number{0};
            runLawful(s, false, "zero shares with nonzero assets");
        }
        {
            auto s = baseline();
            s.assetsMaximum = Number{3};  // below the total of 5
            runLawful(s, false, "assetsTotal above assetsMaximum");
        }
        {
            auto s = baseline();
            s.lossUnrealized = Number{-1};
            runLawful(s, false, "negative lossUnrealized");
        }
        // Loss above the total-minus-available gap (gap 2, loss 4), staying below the total.
        {
            auto s = baseline();
            s.assetsAvailable = Number{3};
            s.lossUnrealized = Number{4};
            runLawful(s, false, "lossUnrealized above the loss gap");
        }
        // Loss above the total. With available 0 the gap equals the total, so this also breaks
        // lossUnrealized_le
        {
            auto s = baseline();
            s.assetsAvailable = Number{0};
            s.lossUnrealized = Number{6};
            runLawful(s, false, "lossUnrealized above assetsTotal");
        }
    }

    void
    runTests() override
    {
        testBaseline();
        testWellFormed();
        testValid();
    }
};

BEAST_DEFINE_TESTSUITE(LeanLawfulVault, formal_verification, xrpl);

}  // namespace xrpl::test
