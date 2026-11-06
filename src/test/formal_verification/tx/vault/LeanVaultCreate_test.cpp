#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/protocol/NumericTypeFFI.h>
#include <test/formal_verification/ffi/vault/VaultCreateFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/CreateSetSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/mpt.h>
#include <test/jtx/ter.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/tx/apply.h>

#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

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

    // The shared ledger's assets: XRP, an IOU and an MPT.
    struct CreateAssets
    {
        Asset xrp;
        Asset iou;
        Asset mpt;
    };

    // Model of VaultCreate: canCreate is preclaim, create is the vault doApply writes. A preflight
    // rejection (tem) is matched by create rejecting the fields as not lawful, unless the check is
    // `outsideModel`: the model then normalizes the field instead of rejecting it. The C++ side
    // applies on a throwaway copy of the open ledger; returns its verdict.
    TER
    checkCreate(
        jtx::Env& env,
        jtx::Account const& owner,
        Asset const& asset,
        VaultCreateArgs args,
        bool outsideModel = false)
    {
        args.numericType = NumericTypeFFI::tagOf(asset);
        std::uint32_t const now = parentCloseTime(env);
        LawfulTerResult const canCreate = leanCanVaultCreate(args, now);
        LeanCreateResult const created = leanVaultCreate(args);

        jtx::Vault vault{env};
        auto [tx, vaultKeylet] = vault.create(
            {.owner = owner,
             .asset = asset,
             .flags = args.ownerCanBlockDeposit
                 ? std::optional<std::uint32_t>{tfVaultOwnerCanBlockDeposit}
                 : std::nullopt,
             .vaultKind = args.subscriptionDate
                 ? std::optional<std::uint8_t>{std::to_underlying(VaultKind::ClosedEnded)}
                 : std::nullopt,
             .subscriptionDate = args.subscriptionDate,
             .redemptionDate = args.redemptionDate,
             .earlyExitFeeRate = args.earlyExitFeeRate});
        if (args.scale)
            tx[sfScale] = *args.scale;
        if (args.assetsMaximum)
            tx[sfAssetsMaximum] = *args.assetsMaximum;
        OpenView view{*env.current()};
        auto const jt = env.jt(tx);
        TER const cppTer = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;

        std::string const at = argsText(args, now) + " cpp=" + transToken(cppTer) + ": ";
        BEAST_EXPECTS(!canCreate.leanError.has_value(), at + "lean canCreate error");
        if (isTemMalformed(cppTer))
        {
            if (outsideModel)
                BEAST_EXPECTS(
                    !created.leanError.has_value(), at + "the model does not normalize the field");
            else
                BEAST_EXPECTS(
                    created.leanError == LeanError::notLawful,
                    at +
                        "preflight rejects the fields but the model creates the vault (canCreate " +
                        transToken(canCreate.ter) + ")");
            return cppTer;
        }
        BEAST_EXPECTS(canCreate.ter == cppTer, at + "lean=" + transToken(canCreate.ter));
        if (cppTer != tesSUCCESS)
            return cppTer;

        BEAST_EXPECTS(!created.leanError.has_value(), at + "lean create error");
        Vault const cpp = readVaultState(view, vaultKeylet, asset);
        Vault const& lean = created.vault;
        BEAST_EXPECTS(
            lean.scale == cpp.scale,
            at + "scale lean=" + std::to_string(lean.scale) + " cpp=" + std::to_string(cpp.scale));
        BEAST_EXPECTS(
            lean.assetsMaximum == cpp.assetsMaximum,
            at + "assetsMaximum lean=" +
                (lean.assetsMaximum ? to_string(*lean.assetsMaximum) : "none") +
                " cpp=" + (cpp.assetsMaximum ? to_string(*cpp.assetsMaximum) : "none"));
        BEAST_EXPECTS(lean.subscriptionDate == cpp.subscriptionDate, at + "subscription date");
        BEAST_EXPECTS(lean.redemptionDate == cpp.redemptionDate, at + "redemption date");
        BEAST_EXPECTS(lean.earlyExitFeeRate == cpp.earlyExitFeeRate, at + "early-exit fee rate");
        BEAST_EXPECT(lean.ownerCanBlockDeposit == cpp.ownerCanBlockDeposit);
        BEAST_EXPECT(lean.depositBlocked == cpp.depositBlocked);
        BEAST_EXPECT(lean.assetsTotal == cpp.assetsTotal && cpp.assetsTotal == Number{0});
        BEAST_EXPECT(lean.sharesTotal == cpp.sharesTotal && cpp.sharesTotal == Number{0});
        return cppTer;
    }

    static std::string
    argsText(VaultCreateArgs const& args, std::uint32_t now)
    {
        std::string t = "scale " + (args.scale ? std::to_string(*args.scale) : "default") +
            " maximum " + (args.assetsMaximum ? to_string(*args.assetsMaximum) : "none");
        if (args.subscriptionDate)
            t += " subscription P" + std::to_string(std::int64_t{*args.subscriptionDate} - now) +
                " redemption P" + std::to_string(std::int64_t{*args.redemptionDate} - now);
        if (args.earlyExitFeeRate)
            t += " fee " + std::to_string(*args.earlyExitFeeRate);
        return t;
    }

    void
    runVaultCreate(
        jtx::Env& env,
        jtx::Account const& owner,
        CreateAssets const& assets,
        std::string const& label,
        AssetKind kind,
        VaultCreateArgs args,
        std::optional<ScheduleOffsets> schedule,
        TER expected,
        bool outsideModel = false)
    {
        testcase(label);
        Asset const asset = kind == AssetKind::iou ? assets.iou
            : kind == AssetKind::mpt               ? assets.mpt
                                                   : assets.xrp;
        if (schedule)
        {
            args.subscriptionDate =
                static_cast<std::uint32_t>(parentCloseTime(env) + schedule->subscription);
            args.redemptionDate = *args.subscriptionDate + schedule->investmentPeriod;
        }
        TER const cppTer = checkCreate(env, owner, asset, args, outsideModel);
        BEAST_EXPECTS(
            cppTer == expected,
            std::string("cpp=") + transToken(cppTer) + " expected " + transToken(expected));
    }

    // ---- Sweeps --------------------------------------------------------------------------------

    using SweepAssets = std::vector<Asset>;

    static std::string
    assetName(Asset const& asset)
    {
        return asset.native() ? "XRP" : asset.holds<MPTIssue>() ? "MPT" : "IOU";
    }

    // A schedule closed-ended vault with fee field `fee`, subscribing 600 s from now.
    static VaultCreateArgs
    scheduled(jtx::Env& env, std::optional<std::uint32_t> fee = std::nullopt)
    {
        std::uint32_t const sub = parentCloseTime(env) + 600;
        return {
            .subscriptionDate = sub, .redemptionDate = sub + 1'000'000, .earlyExitFeeRate = fee};
    }

    void
    testScheduleSweep(jtx::Env& env, jtx::Account const& owner, SweepAssets const& assets)
    {
        for (Asset const& asset : assets)
        {
            sweepSchedule(env, owner, asset);
        }
    }

    // A subscription date at or before the parent close time P is tecEXPIRED, and an investment
    // period outside [180, 946'708'560) is malformed. Rows sit at P with the gap on each bound.
    void
    sweepSchedule(jtx::Env& env, jtx::Account const& owner, Asset const& asset)
    {
        beginCase(("create " + assetName(asset) + " schedule-Sweep").c_str());
        std::uint32_t const now = parentCloseTime(env);
        runAroundCusp(kScheduleCases, [&](ScheduleCusp const& c) {
            std::uint32_t const sub = static_cast<std::uint32_t>(now + c.subscription);
            VaultCreateArgs const args{
                .subscriptionDate = sub, .redemptionDate = static_cast<std::uint32_t>(sub + c.gap)};
            return checkCreate(env, owner, asset, args);
        });
    }

    void
    testEarlyExitFeeSweep(jtx::Env& env, jtx::Account const& owner, SweepAssets const& assets)
    {
        for (Asset const& asset : assets)
        {
            sweepEarlyExitFee(env, owner, asset);
        }
    }

    // An early-exit fee rate above 100'000 tenth-bips (100%) is malformed.
    void
    sweepEarlyExitFee(jtx::Env& env, jtx::Account const& owner, Asset const& asset)
    {
        beginCase(("create " + assetName(asset) + " early-exit fee-Sweep").c_str());
        runAroundCusp(kEarlyExitFeeCases, [&](std::int64_t rate) {
            return checkCreate(env, owner, asset, scheduled(env, static_cast<std::uint32_t>(rate)));
        });
    }

    // An IOU vault scale above 10 is malformed.
    void
    testScaleSweep(jtx::Env& env, jtx::Account const& owner, Asset const& iou)
    {
        beginCase("create IOU scale-Sweep");
        runAroundCusp(kScaleCases, [&](std::int64_t scale) {
            return checkCreate(env, owner, iou, {.scale = static_cast<std::uint8_t>(scale)});
        });
    }

    void
    testMaximumSignSweep(jtx::Env& env, jtx::Account const& owner, SweepAssets const& assets)
    {
        for (Asset const& asset : assets)
        {
            sweepMaximumSign(env, owner, asset);
        }
    }

    // A negative AssetsMaximum is malformed; 0 means no cap. Values in grid steps of the default
    // scale.
    void
    sweepMaximumSign(jtx::Env& env, jtx::Account const& owner, Asset const& asset)
    {
        beginCase(("create " + assetName(asset) + " maximum sign-Sweep").c_str());
        int const exponent = asset.holds<Issue>() && !asset.native() ? -6 : 0;
        runAroundCusp(kMaximumSignCases, [&](std::int64_t steps) {
            return checkCreate(env, owner, asset, {.assetsMaximum = Number{steps, exponent}});
        });
    }

    void
    testMaximumGridSweep(jtx::Env& env, jtx::Account const& owner, Asset const& iou)
    {
        for (std::uint8_t const scale : {0, 6, 10})
        {
            sweepMaximumGrid(env, owner, iou, scale);
        }
    }

    // An IOU AssetsMaximum off the vault grid 10^-scale, or with more than 16 digits, is
    // tecPRECISION_LOSS. Rows are on the grid; moving the mantissa leaves it.
    void
    sweepMaximumGrid(jtx::Env& env, jtx::Account const& owner, Asset const& iou, std::uint8_t scale)
    {
        beginCase(("create IOU scale " + std::to_string(scale) + " maximum grid-Sweep").c_str());
        runAroundCusp(kMaximumGridCases, [&](MaximumGridCusp const& c) {
            Number const maximum{c.mantissa, static_cast<int>(c.exponent) - scale};
            return checkCreate(env, owner, iou, {.scale = scale, .assetsMaximum = maximum});
        });
    }

    // An XRP AssetsMaximum above 1e17 drops is not representable: C++ preflight is temMALFORMED.
    void
    testXrpMaximumSweep(jtx::Env& env, jtx::Account const& owner, Asset const& xrp)
    {
        beginCase("create XRP maximum range-Sweep");
        runAroundCusp(kXrpMaximumCases, [&](std::int64_t drops) {
            return checkCreate(env, owner, xrp, {.assetsMaximum = Number{drops}});
        });
    }

    void
    runTests() override
    {
        using namespace jtx;
        // One ledger; every create (old tests and sweeps) applies on a throwaway view of it.
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        env.close();
        CreateAssets const assets{
            .xrp = xrpIssue(), .iou = issuer["USD"].asset(), .mpt = mptt.issuanceID()};

        // Open-ended vaults: the scale defaults to 6 for an IOU and is 0 for XRP and MPT.
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU vault, default scale",
            AssetKind::iou,
            {},
            std::nullopt,
            tesSUCCESS);
        runVaultCreate(
            env, owner, assets, "MPT vault", AssetKind::mpt, {}, std::nullopt, tesSUCCESS);
        runVaultCreate(
            env,
            owner,
            assets,
            "XRP vault with a maximum",
            AssetKind::xrp,
            {.assetsMaximum = Number{1'000}},
            std::nullopt,
            tesSUCCESS);
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU vault, owner can block deposits",
            AssetKind::iou,
            {.ownerCanBlockDeposit = true},
            std::nullopt,
            tesSUCCESS);

        // AssetsMaximum must lie on the 10^-scale grid.
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU maximum on the scale-2 grid",
            AssetKind::iou,
            {.scale = 2, .assetsMaximum = Number{100'001, -2}},
            std::nullopt,
            tesSUCCESS);
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU maximum off the scale-2 grid",
            AssetKind::iou,
            {.scale = 2, .assetsMaximum = Number{1'001, -3}},
            std::nullopt,
            tecPRECISION_LOSS);
        // FV_M2_19 (regression): a 17-digit AssetsMaximum used to be rounded to the STAmount grid
        // on create, storing a different cap than submitted. It is now rejected upfront.
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU maximum over 16 digits",
            AssetKind::iou,
            {.assetsMaximum = Number{12'345'678'901'234'567LL, -1}},
            std::nullopt,
            tecPRECISION_LOSS);
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU scale above 10",
            AssetKind::iou,
            {.scale = 11},
            std::nullopt,
            temMALFORMED);
        // A scale on an integral asset is a preflight error; the model forces the scale to 0.
        runVaultCreate(
            env,
            owner,
            assets,
            "XRP vault with a scale",
            AssetKind::xrp,
            {.scale = 3},
            std::nullopt,
            temMALFORMED,
            true);
        runVaultCreate(
            env,
            owner,
            assets,
            "MPT vault with a scale",
            AssetKind::mpt,
            {.scale = 3},
            std::nullopt,
            temMALFORMED,
            true);
        // A zero maximum means no cap; a negative one is rejected.
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU vault with a zero maximum",
            AssetKind::iou,
            {.assetsMaximum = Number{0}},
            std::nullopt,
            tesSUCCESS);
        runVaultCreate(
            env,
            owner,
            assets,
            "IOU vault with a negative maximum",
            AssetKind::iou,
            {.assetsMaximum = Number{-1}},
            std::nullopt,
            temMALFORMED);

        // Closed-ended vaults.
        runVaultCreate(
            env,
            owner,
            assets,
            "closed-ended IOU vault with an early-exit fee",
            AssetKind::iou,
            {.earlyExitFeeRate = 5'000},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 1'000'000},
            tesSUCCESS);
        runVaultCreate(
            env,
            owner,
            assets,
            "closed-ended vault subscribing one second from now",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 1, .investmentPeriod = 180},
            tesSUCCESS);
        runVaultCreate(
            env,
            owner,
            assets,
            "closed-ended vault whose subscription date is now",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 0, .investmentPeriod = 180},
            tecEXPIRED);
        runVaultCreate(
            env,
            owner,
            assets,
            "closed-ended investment period below 180 s",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 179},
            temMALFORMED);
        // The investment period must stay below 30 years (946'708'560 s).
        runVaultCreate(
            env,
            owner,
            assets,
            "closed-ended investment period just below 30 years",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 946'708'559},
            tesSUCCESS);
        runVaultCreate(
            env,
            owner,
            assets,
            "closed-ended investment period of 30 years",
            AssetKind::iou,
            {},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 946'708'560},
            temMALFORMED);
        runVaultCreate(
            env,
            owner,
            assets,
            "closed-ended early-exit fee above 100%",
            AssetKind::iou,
            {.earlyExitFeeRate = 100'001},
            ScheduleOffsets{.subscription = 60, .investmentPeriod = 1'000'000},
            temMALFORMED);
        // An early-exit fee, even zero, needs a closed-ended vault.
        runVaultCreate(
            env,
            owner,
            assets,
            "open-ended vault with an early-exit fee",
            AssetKind::iou,
            {.earlyExitFeeRate = 5'000},
            std::nullopt,
            temMALFORMED);
        runVaultCreate(
            env,
            owner,
            assets,
            "open-ended vault with a zero early-exit fee",
            AssetKind::iou,
            {.earlyExitFeeRate = 0},
            std::nullopt,
            temMALFORMED);

        SweepAssets const all{assets.xrp, assets.iou, assets.mpt};
        testScheduleSweep(env, owner, all);
        testEarlyExitFeeSweep(env, owner, all);
        testScaleSweep(env, owner, assets.iou);
        testMaximumSignSweep(env, owner, all);
        testMaximumGridSweep(env, owner, assets.iou);
        testXrpMaximumSweep(env, owner, assets.xrp);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultCreate, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
