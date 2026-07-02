#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/vault/deposit.h>
#include <test/formal_verification/ffi/vault/state.h>
#include <test/jtx.h>
#include <test/jtx/ter.h>

#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/TER.h>

#include <cstdint>
#include <optional>
#include <string>

namespace xrpl::test {

using namespace formal_verification;

class LeanVaultDeposit_test : public LeanSuite
{
    // Share MPToken ceiling. Fresh-vault deposit computes shares ~ amount * 10^scale,
    // which must stay <= this or doApply throws and returns tecPATH_DRY.
    static constexpr std::int64_t kMaxMptShares = 9'223'372'036'854'775'807LL;  // 2^63 - 1

    enum class Kind { XRP, IOU, MPT };
    enum class Mag { Min, Avg, Max, OverMax };

    static char const*
    kindName(Kind k)
    {
        switch (k)
        {
            case Kind::XRP:
                return "XRP";
            case Kind::IOU:
                return "IOU";
            case Kind::MPT:
                return "MPT";
        }
        return "?";
    }

    static char const*
    magName(Mag m)
    {
        switch (m)
        {
            case Mag::Min:
                return "min";
            case Mag::Avg:
                return "avg";
            case Mag::Max:
                return "max";
            case Mag::OverMax:
                return "over-max";
        }
        return "?";
    }

    static Keylet
    createVault(
        jtx::Env& env,
        jtx::Account const& owner,
        Asset const& asset,
        std::optional<std::uint32_t> flags = {})
    {
        jtx::Vault vault{env};
        auto const [jv, keylet] = vault.create({.owner = owner, .asset = asset, .flags = flags});
        env(jv);
        env.close();
        return keylet;
    }

    // The deposit amount for a (kind, magnitude). `asset(n)` yields the right STAmount per
    // kind; `vaultScale` bounds the IOU maximum via the share ceiling.
    static STAmount
    amountFor(Kind kind, Mag mag, jtx::PrettyAsset const& asset, std::uint8_t vaultScale)
    {
        using namespace jtx;

        // Largest deposit whose shares (~amount * 10^scale) still fit under kMaxMptShares.
        auto iouMax = [&]() -> std::int64_t {
            std::int64_t pow = 1;
            for (std::uint8_t i = 0; i < vaultScale; ++i)
                pow *= 10;
            return kMaxMptShares / pow;  // (iouMax + 1) * pow always exceeds the ceiling
        };

        switch (kind)
        {
            case Kind::XRP:  // scale 0; bounded by supply/fundability, not the share ceiling
                switch (mag)
                {
                    case Mag::Min:
                        return drops(1);
                    case Mag::Avg:
                        return XRP(1'000);
                    case Mag::Max:
                        return XRP(80'000'000'000);  // 8e16 drops, well under cMaxNative (1e17)
                    case Mag::OverMax:
                        return XRP(80'000'000'000);  // no share overflow for XRP; unused
                }
                break;
            case Kind::IOU:  // max ~ kMaxMptShares / 10^scale
                switch (mag)
                {
                    case Mag::Min:
                        return asset(1);
                    case Mag::Avg:
                        return asset(1'000);
                    case Mag::Max:
                        return asset(iouMax());
                    case Mag::OverMax:
                        return asset(iouMax() + 1);  // shares overflow -> tecPATH_DRY in doApply
                }
                break;
            case Kind::MPT:  // scale 0
                switch (mag)
                {
                    case Mag::Min:
                        return asset(1);
                    case Mag::Avg:
                        return asset(1'000);
                    case Mag::Max:
                        return asset(kMaxMptShares);  // 2^63 - 1
                    case Mag::OverMax:
                        return asset(kMaxMptShares);  // not representable above max; unused
                }
                break;
        }
        return STAmount{};
    }

    // Run one deposit scenario differentially. `expected` is the correct TER; both the full
    // C++ transaction and the preclaim model are checked against it. A gap in the model (e.g.
    // it does not yet cover the doApply share-overflow -> tecPATH_DRY) shows up as a failure.
    void
    testDeposit(Kind kind, Mag mag, bool depositorIsIssuer, TER expected)
    {
        using namespace jtx;
        testcase(
            std::string("deposit ") + kindName(kind) + " " + magName(mag) +
            (depositorIsIssuer ? " (issuer)" : ""));

        Env env(*this);
        Account const vaultOwner{"vaultOwner"};
        Account const issuer{"issuer"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), vaultOwner, issuer);
        env.close();

        // --- per-kind asset + depositor + holder setup ---
        PrettyAsset asset = xrpIssue();
        Account depositor = holder;
        switch (kind)
        {
            case Kind::XRP:
                asset = xrpIssue();
                depositor = holder;  // no issuer concept for XRP; holder funded below
                break;

            case Kind::IOU:
                asset = issuer["USD"];
                depositor = depositorIsIssuer ? issuer : holder;
                if (!depositorIsIssuer)
                {
                    env.fund(XRP(1'000'000), holder);
                    env.close();
                    // limit large enough to cover any Max/OverMax amount
                    env(trust(holder, asset(10'000'000'000'000'000LL)));
                    env.close();
                }
                break;

            case Kind::MPT: {
                MPTTester mptt{env, issuer, kMptInitNoFund};
                mptt.create({.flags = tfMPTCanTransfer});
                asset = mptt.issuanceID();
                depositor = holder;
                env.fund(XRP(1'000'000), holder);
                env.close();
                mptt.authorize({.account = holder});
                env.close();
                break;
            }
        }

        auto const vaultKeylet = createVault(env, vaultOwner, asset.raw());
        auto const vaultSle = env.le(vaultKeylet);
        BEAST_EXPECT(vaultSle);
        std::uint8_t const scale = vaultSle->isFieldPresent(sfScale) ? vaultSle->at(sfScale) : 0;

        STAmount const amount = amountFor(kind, mag, asset, scale);

        // Fund the depositor so the amount is actually held (the issuer is the source).
        if (!depositorIsIssuer)
        {
            if (kind == Kind::XRP)
            {
                env.fund(STAmount(amount) + XRP(1'000'000), holder);
            }
            else
            {
                env(pay(issuer, holder, amount));
            }
            env.close();
        }

        // Fresh vault: assetsTotal is zero.
        VaultState const state{.assetsTotal = Number{0}, .asset = asset.raw()};

        std::optional<STAmount> const accountBalance = depositorIsIssuer
            ? std::nullopt
            : std::optional<STAmount>{
                  kind == Kind::XRP ? STAmount(env.balance(depositor))
                                    : STAmount(env.balance(depositor, asset.raw()))};

        LeanTerResult const lean = leanCanDeposit(state, amount, accountBalance);
        BEAST_EXPECTS(!lean.threw, "lean canDeposit raised");

        env(Vault::deposit({.depositor = depositor, .id = vaultKeylet.key, .amount = amount}),
            jtx::Ter(std::ignore));
        TER const cppTer = env.ter();
        env.close();

        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
        BEAST_EXPECTS(
            TER::fromInt(lean.code) == expected,
            std::string("lean=") + transToken(TER::fromInt(lean.code)) + " expected " +
                transToken(expected));
    }

    void
    testDepositScenarios()
    {
        using namespace jtx;
        //          kind        magnitude       issuer  expected

        // XRP: scale 0, no share overflow within the XRP domain.
        testDeposit(Kind::XRP, Mag::Min, false, tesSUCCESS);
        testDeposit(Kind::XRP, Mag::Avg, false, tesSUCCESS);
        testDeposit(Kind::XRP, Mag::Max, false, tesSUCCESS);

        // IOU, holder as depositor.
        testDeposit(Kind::IOU, Mag::Min, false, tesSUCCESS);
        testDeposit(Kind::IOU, Mag::Avg, false, tesSUCCESS);
        testDeposit(Kind::IOU, Mag::Max, false, tesSUCCESS);
        // Over the share ceiling: doApply overflow -> tecPATH_DRY. The preclaim model does not
        // cover this yet, so this case FAILS on the lean side, representing the gap.
        testDeposit(Kind::IOU, Mag::OverMax, false, tecPATH_DRY);

        // IOU, issuer as depositor (accountBalance = none in the model).
        testDeposit(Kind::IOU, Mag::Min, true, tesSUCCESS);
        testDeposit(Kind::IOU, Mag::Avg, true, tesSUCCESS);
        testDeposit(Kind::IOU, Mag::Max, true, tesSUCCESS);
        testDeposit(Kind::IOU, Mag::OverMax, true, tecPATH_DRY);

        // MPT: scale 0; max deposit is the MPT ceiling itself.
        testDeposit(Kind::MPT, Mag::Min, false, tesSUCCESS);
        testDeposit(Kind::MPT, Mag::Avg, false, tesSUCCESS);
        testDeposit(Kind::MPT, Mag::Max, false, tesSUCCESS);
    }

    void
    runTests() override
    {
        testDepositScenarios();
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultDeposit, formal_verification, xrpl);

}  // namespace xrpl::test
