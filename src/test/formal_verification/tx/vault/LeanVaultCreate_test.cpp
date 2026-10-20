#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/vault/VaultCreateFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>
#include <test/jtx/ter.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>

#include <cstdint>
#include <optional>
#include <string>
#include <utility>

namespace xrpl::test::formal_verification {

class LeanVaultCreate_test : public LeanSuite
{
    enum class AssetKind { xrp, iou, mpt };

    // A closed-ended schedule, as offsets from the parent close time.
    struct ScheduleOffsets
    {
        std::int64_t subscription;
        std::uint32_t investmentPeriod;
    };

    // Model of VaultCreate: canCreate is preclaim, create is the vault doApply writes. A preflight
    // rejection (tem) is matched by create rejecting the fields as not lawful.
    void
    runVaultCreate(
        std::string const& label,
        AssetKind kind,
        VaultCreateArgs args,
        std::optional<ScheduleOffsets> schedule,
        TER expected)
    {
        using namespace jtx;
        testcase(label);

        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();

        Asset asset = xrpIssue();
        if (kind == AssetKind::iou)
            asset = issuer["USD"].asset();
        else if (kind == AssetKind::mpt)
        {
            MPTTester mptt{env, issuer, kMptInitNoFund};
            mptt.create({.flags = tfMPTCanTransfer});
            asset = mptt.issuanceID();
        }
        args.numericType = NumericTypeFFI::tagOf(asset);

        std::uint32_t const now = parentCloseTime(env);
        if (schedule)
        {
            args.subscriptionDate = static_cast<std::uint32_t>(now + schedule->subscription);
            args.redemptionDate = *args.subscriptionDate + schedule->investmentPeriod;
        }

        LawfulTerResult const canCreate = leanCanVaultCreate(args, now);
        LeanCreateResult const created = leanVaultCreate(args);

        jtx::Vault vault{env};
        auto [tx, vaultKeylet] = vault.create(
            {.owner = owner,
             .asset = asset,
             .flags = args.ownerCanBlockDeposit
                 ? std::optional<std::uint32_t>{tfVaultOwnerCanBlockDeposit}
                 : std::nullopt,
             .vaultKind = schedule
                 ? std::optional<std::uint8_t>{std::to_underlying(VaultKind::ClosedEnded)}
                 : std::nullopt,
             .subscriptionDate = args.subscriptionDate,
             .redemptionDate = args.redemptionDate,
             .earlyExitFeeRate = args.earlyExitFeeRate});
        if (args.scale)
            tx[sfScale] = *args.scale;
        if (args.assetsMaximum)
            tx[sfAssetsMaximum] = *args.assetsMaximum;
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
                "preflight rejects the fields but the model creates the vault");
            return;
        }
        BEAST_EXPECTS(
            canCreate.ter == cppTer,
            std::string("lean=") + transToken(canCreate.ter) + " cpp=" + transToken(cppTer));
        if (cppTer != tesSUCCESS)
            return;

        BEAST_EXPECTS(!created.leanError.has_value(), "lean create error");
        Vault const cpp = readVaultState(env, vaultKeylet, asset);
        Vault const& lean = created.vault;
        BEAST_EXPECTS(
            lean.scale == cpp.scale,
            "scale lean=" + std::to_string(lean.scale) + " cpp=" + std::to_string(cpp.scale));
        BEAST_EXPECTS(
            lean.assetsMaximum == cpp.assetsMaximum,
            "assetsMaximum lean=" + (lean.assetsMaximum ? to_string(*lean.assetsMaximum) : "none") +
                " cpp=" + (cpp.assetsMaximum ? to_string(*cpp.assetsMaximum) : "none"));
        BEAST_EXPECT(lean.subscriptionDate == cpp.subscriptionDate);
        BEAST_EXPECT(lean.redemptionDate == cpp.redemptionDate);
        BEAST_EXPECT(lean.earlyExitFeeRate == cpp.earlyExitFeeRate);
        BEAST_EXPECT(lean.ownerCanBlockDeposit == cpp.ownerCanBlockDeposit);
        BEAST_EXPECT(lean.depositBlocked == cpp.depositBlocked);
        BEAST_EXPECT(lean.assetsTotal == cpp.assetsTotal && cpp.assetsTotal == Number{0});
        BEAST_EXPECT(lean.sharesTotal == cpp.sharesTotal && cpp.sharesTotal == Number{0});
    }

    void
    runTests() override
    {
        // Open-ended vaults: the scale defaults to 6 for an IOU and is 0 for XRP and MPT.
        runVaultCreate("IOU vault, default scale", AssetKind::iou, {}, std::nullopt, tesSUCCESS);
        runVaultCreate("MPT vault", AssetKind::mpt, {}, std::nullopt, tesSUCCESS);
        runVaultCreate(
            "XRP vault with a maximum",
            AssetKind::xrp,
            {.assetsMaximum = Number{1'000}},
            std::nullopt,
            tesSUCCESS);
        runVaultCreate(
            "IOU vault, owner can block deposits",
            AssetKind::iou,
            {.ownerCanBlockDeposit = true},
            std::nullopt,
            tesSUCCESS);

        // AssetsMaximum must lie on the 10^-scale grid.
        runVaultCreate(
            "IOU maximum on the scale-2 grid",
            AssetKind::iou,
            {.scale = 2, .assetsMaximum = Number{100'001, -2}},
            std::nullopt,
            tesSUCCESS);
        runVaultCreate(
            "IOU maximum off the scale-2 grid",
            AssetKind::iou,
            {.scale = 2, .assetsMaximum = Number{1'001, -3}},
            std::nullopt,
            tecPRECISION_LOSS);
        // FV_M2_19 (regression): a 17-digit AssetsMaximum used to be rounded to the STAmount grid
        // on create, storing a different cap than submitted. It is now rejected upfront.
        runVaultCreate(
            "IOU maximum over 16 digits",
            AssetKind::iou,
            {.assetsMaximum = Number{12'345'678'901'234'567LL, -1}},
            std::nullopt,
            tecPRECISION_LOSS);
        runVaultCreate(
            "IOU scale above 10", AssetKind::iou, {.scale = 11}, std::nullopt, temMALFORMED);

        // Closed-ended vaults.
        runVaultCreate(
            "closed-ended IOU vault with an early-exit fee",
            AssetKind::iou,
            {.earlyExitFeeRate = 5'000},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 1'000'000},
            tesSUCCESS);
        runVaultCreate(
            "closed-ended vault subscribing one second from now",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 1, .investmentPeriod = 180},
            tesSUCCESS);
        runVaultCreate(
            "closed-ended vault whose subscription date is now",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 0, .investmentPeriod = 180},
            tecEXPIRED);
        runVaultCreate(
            "closed-ended investment period below 180 s",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 179},
            temMALFORMED);
        runVaultCreate(
            "closed-ended early-exit fee above 100%",
            AssetKind::iou,
            {.earlyExitFeeRate = 100'001},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 1'000'000},
            temMALFORMED);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultCreate, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
