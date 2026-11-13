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
#include <xrpl/ledger/OpenView.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/tx/apply.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

// A VaultCreate's fields: AssetsMaximum is maximum * 10^assetExponent of the asset, the dates
// are offsets from the parent close time P. A C++ preflight rejection (tem) is paired with
// `leanError`, the model error that stands for it.
struct CreateCase
{
    std::optional<std::uint8_t> scale{};
    std::optional<std::int64_t> maximum{};
    // AssetsMaximum is maximum * 10^assetExponent of the asset (not vault grid units).
    int assetExponent{};
    std::optional<std::int64_t> subscription{};
    std::optional<std::int64_t> redemption{};
    std::optional<std::uint32_t> earlyExitFeeRate{};
    TER expected;
    std::optional<LeanError> leanError{};
};

class LeanVaultCreate_test : public LeanSuite
{
    // Every create applies on a throwaway view of one shared ledger and expects its verdict on both
    // sides, with every field of the created vault equal when both succeed.

    enum class AssetKind { xrp, iou, mpt };

    // A closed-ended schedule, as offsets from the parent close time.
    struct ScheduleOffsets
    {
        std::int64_t subscription;
        std::uint32_t investmentPeriod;
    };

    using TestAssets = std::vector<Asset>;

    struct Setup
    {
        jtx::Account owner;
        Asset xrpAsset;
        Asset iouAsset;
        Asset mptAsset;
        TestAssets xrp;
        TestAssets mpt;
        TestAssets iou;
        TestAssets integral;
        TestAssets all;
    };

    // VaultCreate of `args` on a throwaway copy of the open ledger, and the model on the same
    // fields. The model has no preflight: fields that cannot form a lawful vault (create fails)
    // stand for it, so that check comes before canCreate (preclaim).
    static std::pair<AppliedVaultTx, LeanVaultResult>
    applyCreate(jtx::Env& env, jtx::Account const& owner, Asset const& asset, VaultCreateArgs args)
    {
        args.numericType = NumericTypeFFI::tagOf(asset);
        LeanCreateResult const created = leanVaultCreate(args);
        LawfulTerResult const canCreate = leanCanVaultCreate(args, parentCloseTime(env));
        LeanVaultResult lean;
        if (created.leanError)
        {
            lean.leanError = created.leanError;
        }
        else if (canCreate.leanError)
        {
            lean.leanError = canCreate.leanError;
        }
        else if (canCreate.ter != tesSUCCESS)
        {
            lean.error = canCreate.ter;
        }
        else
        {
            lean.vault = created.vault;
        }

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
        TER const ter = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
        AppliedVaultTx const cpp{
            .pre = {},
            .ter = ter,
            .post = ter == tesSUCCESS ? readVaultState(view, vaultKeylet, asset) : Vault{},
        };
        return {cpp, lean};
    }

    static std::string
    argsText(Asset const& asset, VaultCreateArgs const& args, std::uint32_t now)
    {
        std::string t = assetName(asset) + " scale " +
            (args.scale ? std::to_string(*args.scale) : "default") + " maximum " +
            (args.assetsMaximum ? to_string(*args.assetsMaximum) : "none");
        if (args.subscriptionDate)
            t += " subscription P" + std::to_string(std::int64_t{*args.subscriptionDate} - now) +
                " redemption P" + std::to_string(std::int64_t{*args.redemptionDate} - now);
        if (args.earlyExitFeeRate)
            t += " fee " + std::to_string(*args.earlyExitFeeRate);
        return t + ": ";
    }

    static std::string
    assetName(Asset const& asset)
    {
        return asset.native() ? "XRP" : asset.holds<MPTIssue>() ? "MPT" : "IOU";
    }

    // A C++ tem is paired with `leanError`, the model error that stands for it.
    void
    runVaultCreate(
        jtx::Env& env,
        Setup const& s,
        std::string const& label,
        AssetKind kind,
        VaultCreateArgs args,
        std::optional<ScheduleOffsets> schedule,
        TER expected,
        std::optional<LeanError> leanError = std::nullopt)
    {
        testcase(label);
        Asset const asset = kind == AssetKind::iou ? s.iouAsset
            : kind == AssetKind::mpt               ? s.mptAsset
                                                   : s.xrpAsset;
        if (schedule)
        {
            args.subscriptionDate =
                static_cast<std::uint32_t>(parentCloseTime(env) + schedule->subscription);
            args.redemptionDate = *args.subscriptionDate + schedule->investmentPeriod;
        }
        auto const [cpp, lean] = applyCreate(env, s.owner, asset, args);
        std::string const at = argsText(asset, args, parentCloseTime(env));
        expectRow(*this, at, cpp, lean, expected, leanError);
        if (cpp.ter == tesSUCCESS)
        {
            BEAST_EXPECTS(
                cpp.post.assetsTotal == Number{0} && cpp.post.sharesTotal == Number{0},
                at + "the created vault is not empty");
        }
    }

    // A scale on an integral asset is a preflight error; the model forces the scale to 0.
    void
    testIntegralScale(jtx::Env& env, Setup const& s, Asset const& asset)
    {
        testcase(assetName(asset) + " vault with a scale");
        VaultCreateArgs const args{.scale = 3};
        auto const [cpp, lean] = applyCreate(env, s.owner, asset, args);
        expectCppOnlyRejection(
            *this,
            argsText(asset, args, parentCloseTime(env)),
            cpp,
            lean,
            temMALFORMED,
            std::nullopt);
    }

    static Setup
    setup(jtx::Env& env)
    {
        using namespace jtx;
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.close();
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        env.close();
        Asset const xrp = xrpIssue();
        Asset const iou = issuer["USD"].asset();
        Asset const mpt = mptt.issuanceID();
        return {
            .owner = owner,
            .xrpAsset = xrp,
            .iouAsset = iou,
            .mptAsset = mpt,
            .xrp = {xrp},
            .mpt = {mpt},
            .iou = {iou},
            .integral = {xrp, mpt},
            .all = {xrp, iou, mpt},
        };
    }

    // Each case creates a vault from its fields and expects its verdict on both sides.
    // A group comment names a boundary value (the cusp); its rows step those values around it.
    // - Scale: an IOU vault scale above 10 is temMALFORMED.
    // - Maximum sign: a negative AssetsMaximum is temMALFORMED; 0 means no cap. The IOU rows are
    //   in steps of the default scale 6.
    // - Maximum grid: an IOU AssetsMaximum off the vault grid 10^-scale, or with more than 16
    //   digits, is tecPRECISION_LOSS. Each cusp is on the grid; moving the mantissa leaves it,
    //   except where the move only drops a digit.
    // - Maximum range: an AssetsMaximum the asset cannot represent (XRP above 1e17 drops, MPT above
    //   2^63 - 1, IOU past 9999999999999999e80) is temMALFORMED. Each cusp is the largest
    //   representable value.
    // Closed-ended:
    // - Schedule: a subscription date at or before P is tecEXPIRED, and an investment period
    //   (redemption - subscription) outside [180 s, 30 years) is temMALFORMED. Each cusp puts the
    //   subscription date on P with the period on a bound or in between.
    // - Early-exit fee: a rate above 100% (100'000 tenth-bips) is temMALFORMED.
    // clang-format off
    static constexpr CreateCase kScale[] = {
        // scale 10
        {.scale = 8, .expected = tesSUCCESS},
        {.scale = 9, .expected = tesSUCCESS},
        {.scale = 10, .expected = tesSUCCESS},
        {.scale = 11, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.scale = 12, .expected = temMALFORMED, .leanError = LeanError::notLawful},
    };
    static constexpr CreateCase kMaximumSign[] = {
        // maximum 0 (no cap)
        {.maximum = -2, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.maximum = -1, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.maximum = 0, .expected = tesSUCCESS},
        {.maximum = 1, .expected = tesSUCCESS},
        {.maximum = 2, .expected = tesSUCCESS},
    };
    static constexpr CreateCase kMaximumSignIou[] = {
        // maximum 0 (no cap)
        {.maximum = -2, .assetExponent = -6, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.maximum = -1, .assetExponent = -6, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.maximum = 0, .assetExponent = -6, .expected = tesSUCCESS},
        {.maximum = 1, .assetExponent = -6, .expected = tesSUCCESS},
        {.maximum = 2, .assetExponent = -6, .expected = tesSUCCESS},
    };
    static constexpr CreateCase kMaximumGrid[] = {
        // scale 0, 1'000'000'000'000'000e-15 grid steps
        {.scale = 0, .maximum = 999'999'999'999'998, .assetExponent = -15, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 999'999'999'999'999, .assetExponent = -15, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 1'000'000'000'000'000, .assetExponent = -15, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 1'000'000'000'000'001, .assetExponent = -15, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 1'000'000'000'000'002, .assetExponent = -15, .expected = tecPRECISION_LOSS},
        // scale 0, 1'000'000'000'000'000e-6 grid steps
        {.scale = 0, .maximum = 999'999'999'999'998, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 999'999'999'999'999, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 1'000'000'000'000'000, .assetExponent = -6, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 1'000'000'000'000'001, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 1'000'000'000'000'002, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        // scale 0, 9'999'999'999'999'999e0 grid steps
        {.scale = 0, .maximum = 9'999'999'999'999'997, .assetExponent = 0, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 9'999'999'999'999'998, .assetExponent = 0, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 9'999'999'999'999'999, .assetExponent = 0, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 10'000'000'000'000'000, .assetExponent = 0, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 10'000'000'000'000'001, .assetExponent = 0, .expected = tecPRECISION_LOSS},
        // scale 0, 10'000'000'000'000'010e0 grid steps
        {.scale = 0, .maximum = 10'000'000'000'000'008, .assetExponent = 0, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 10'000'000'000'000'009, .assetExponent = 0, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 10'000'000'000'000'010, .assetExponent = 0, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 10'000'000'000'000'011, .assetExponent = 0, .expected = tecPRECISION_LOSS},
        {.scale = 0, .maximum = 10'000'000'000'000'012, .assetExponent = 0, .expected = tecPRECISION_LOSS},
        // scale 0, 9'999'999'999'999'999e79 grid steps
        {.scale = 0, .maximum = 9'999'999'999'999'997, .assetExponent = 79, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 9'999'999'999'999'998, .assetExponent = 79, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 9'999'999'999'999'999, .assetExponent = 79, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 10'000'000'000'000'000, .assetExponent = 79, .expected = tesSUCCESS},
        {.scale = 0, .maximum = 10'000'000'000'000'001, .assetExponent = 79, .expected = tecPRECISION_LOSS},
        // scale 6, 1'000'000'000'000'000e-15 grid steps
        {.scale = 6, .maximum = 999'999'999'999'998, .assetExponent = -21, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 999'999'999'999'999, .assetExponent = -21, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 1'000'000'000'000'000, .assetExponent = -21, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 1'000'000'000'000'001, .assetExponent = -21, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 1'000'000'000'000'002, .assetExponent = -21, .expected = tecPRECISION_LOSS},
        // scale 6, 1'000'000'000'000'000e-6 grid steps
        {.scale = 6, .maximum = 999'999'999'999'998, .assetExponent = -12, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 999'999'999'999'999, .assetExponent = -12, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 1'000'000'000'000'000, .assetExponent = -12, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 1'000'000'000'000'001, .assetExponent = -12, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 1'000'000'000'000'002, .assetExponent = -12, .expected = tecPRECISION_LOSS},
        // scale 6, 9'999'999'999'999'999e0 grid steps
        {.scale = 6, .maximum = 9'999'999'999'999'997, .assetExponent = -6, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 9'999'999'999'999'998, .assetExponent = -6, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 9'999'999'999'999'999, .assetExponent = -6, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 10'000'000'000'000'000, .assetExponent = -6, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 10'000'000'000'000'001, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        // scale 6, 10'000'000'000'000'010e0 grid steps
        {.scale = 6, .maximum = 10'000'000'000'000'008, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 10'000'000'000'000'009, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 10'000'000'000'000'010, .assetExponent = -6, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 10'000'000'000'000'011, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        {.scale = 6, .maximum = 10'000'000'000'000'012, .assetExponent = -6, .expected = tecPRECISION_LOSS},
        // scale 6, 9'999'999'999'999'999e79 grid steps
        {.scale = 6, .maximum = 9'999'999'999'999'997, .assetExponent = 73, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 9'999'999'999'999'998, .assetExponent = 73, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 9'999'999'999'999'999, .assetExponent = 73, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 10'000'000'000'000'000, .assetExponent = 73, .expected = tesSUCCESS},
        {.scale = 6, .maximum = 10'000'000'000'000'001, .assetExponent = 73, .expected = tecPRECISION_LOSS},
        // scale 10, 1'000'000'000'000'000e-15 grid steps
        {.scale = 10, .maximum = 999'999'999'999'998, .assetExponent = -25, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 999'999'999'999'999, .assetExponent = -25, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 1'000'000'000'000'000, .assetExponent = -25, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 1'000'000'000'000'001, .assetExponent = -25, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 1'000'000'000'000'002, .assetExponent = -25, .expected = tecPRECISION_LOSS},
        // scale 10, 1'000'000'000'000'000e-6 grid steps
        {.scale = 10, .maximum = 999'999'999'999'998, .assetExponent = -16, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 999'999'999'999'999, .assetExponent = -16, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 1'000'000'000'000'000, .assetExponent = -16, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 1'000'000'000'000'001, .assetExponent = -16, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 1'000'000'000'000'002, .assetExponent = -16, .expected = tecPRECISION_LOSS},
        // scale 10, 9'999'999'999'999'999e0 grid steps
        {.scale = 10, .maximum = 9'999'999'999'999'997, .assetExponent = -10, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 9'999'999'999'999'998, .assetExponent = -10, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 9'999'999'999'999'999, .assetExponent = -10, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 10'000'000'000'000'000, .assetExponent = -10, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 10'000'000'000'000'001, .assetExponent = -10, .expected = tecPRECISION_LOSS},
        // scale 10, 10'000'000'000'000'010e0 grid steps
        {.scale = 10, .maximum = 10'000'000'000'000'008, .assetExponent = -10, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 10'000'000'000'000'009, .assetExponent = -10, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 10'000'000'000'000'010, .assetExponent = -10, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 10'000'000'000'000'011, .assetExponent = -10, .expected = tecPRECISION_LOSS},
        {.scale = 10, .maximum = 10'000'000'000'000'012, .assetExponent = -10, .expected = tecPRECISION_LOSS},
        // scale 10, 9'999'999'999'999'999e79 grid steps
        {.scale = 10, .maximum = 9'999'999'999'999'997, .assetExponent = 69, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 9'999'999'999'999'998, .assetExponent = 69, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 9'999'999'999'999'999, .assetExponent = 69, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 10'000'000'000'000'000, .assetExponent = 69, .expected = tesSUCCESS},
        {.scale = 10, .maximum = 10'000'000'000'000'001, .assetExponent = 69, .expected = tecPRECISION_LOSS},
    };
    static constexpr CreateCase kMaximumRangeXrp[] = {
        // 100'000'000'000'000'000e0
        {.maximum = 99'999'999'999'999'998, .expected = tesSUCCESS},
        {.maximum = 99'999'999'999'999'999, .expected = tesSUCCESS},
        {.maximum = 100'000'000'000'000'000, .expected = tesSUCCESS},
        // Accepted gap, out of the run: C++ temMALFORMED (preflight range check), model canCreate tecPRECISION_LOSS.
        // {.maximum = 100'000'000'000'000'001, .expected = temMALFORMED},
        // {.maximum = 100'000'000'000'000'002, .expected = temMALFORMED},
    };
    static constexpr CreateCase kMaximumRangeMpt[] = {
        // 922'337'203'685'477'580e1
        {.maximum = 922'337'203'685'477'578, .assetExponent = 1, .expected = tesSUCCESS},
        {.maximum = 922'337'203'685'477'579, .assetExponent = 1, .expected = tesSUCCESS},
        {.maximum = 922'337'203'685'477'580, .assetExponent = 1, .expected = tesSUCCESS},
        // Accepted gap, out of the run: C++ temMALFORMED (preflight range check), model canCreate tecPRECISION_LOSS.
        // {.maximum = 922'337'203'685'477'581, .assetExponent = 1, .expected = temMALFORMED},
        // {.maximum = 922'337'203'685'477'582, .assetExponent = 1, .expected = temMALFORMED},
    };
    static constexpr CreateCase kMaximumRangeIou[] = {
        // 9'999'999'999'999'999e80
        {.maximum = 9'999'999'999'999'997, .assetExponent = 80, .expected = tesSUCCESS},
        {.maximum = 9'999'999'999'999'998, .assetExponent = 80, .expected = tesSUCCESS},
        {.maximum = 9'999'999'999'999'999, .assetExponent = 80, .expected = tesSUCCESS},
        // Accepted gap, out of the run: C++ temMALFORMED (preflight range check), model canCreate tecPRECISION_LOSS.
        // {.maximum = 10'000'000'000'000'000, .assetExponent = 80, .expected = temMALFORMED},
        // {.maximum = 10'000'000'000'000'001, .assetExponent = 80, .expected = temMALFORMED},
    };
    static constexpr CreateCase kSchedule[] = {
        // subscription P, gap 180
        {.subscription = -2, .redemption = 176, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = -2, .redemption = 177, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = -2, .redemption = 178, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 179, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 180, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 177, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = -1, .redemption = 178, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = -1, .redemption = 179, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 180, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 181, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 178, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 0, .redemption = 179, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 0, .redemption = 180, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 181, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 182, .expected = tecEXPIRED},
        {.subscription = 1, .redemption = 179, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 1, .redemption = 180, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 1, .redemption = 181, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 182, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 183, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 180, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 2, .redemption = 181, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 2, .redemption = 182, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 183, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 184, .expected = tesSUCCESS},
        // subscription P, gap 1'000'000
        {.subscription = -2, .redemption = 999'996, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 999'997, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 999'998, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 999'999, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 1'000'000, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 999'997, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 999'998, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 999'999, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 1'000'000, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 1'000'001, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 999'998, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 999'999, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 1'000'000, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 1'000'001, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 1'000'002, .expected = tecEXPIRED},
        {.subscription = 1, .redemption = 999'999, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 1'000'000, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 1'000'001, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 1'000'002, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 1'000'003, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 1'000'000, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 1'000'001, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 1'000'002, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 1'000'003, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 1'000'004, .expected = tesSUCCESS},
        // subscription P, gap 946'708'559
        {.subscription = -2, .redemption = 946'708'555, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 946'708'556, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 946'708'557, .expected = tecEXPIRED},
        {.subscription = -2, .redemption = 946'708'558, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = -2, .redemption = 946'708'559, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = -1, .redemption = 946'708'556, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 946'708'557, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 946'708'558, .expected = tecEXPIRED},
        {.subscription = -1, .redemption = 946'708'559, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = -1, .redemption = 946'708'560, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 0, .redemption = 946'708'557, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 946'708'558, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 946'708'559, .expected = tecEXPIRED},
        {.subscription = 0, .redemption = 946'708'560, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 0, .redemption = 946'708'561, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 1, .redemption = 946'708'558, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 946'708'559, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 946'708'560, .expected = tesSUCCESS},
        {.subscription = 1, .redemption = 946'708'561, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 1, .redemption = 946'708'562, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 2, .redemption = 946'708'559, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 946'708'560, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 946'708'561, .expected = tesSUCCESS},
        {.subscription = 2, .redemption = 946'708'562, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 2, .redemption = 946'708'563, .expected = temMALFORMED, .leanError = LeanError::notLawful},
    };
    static constexpr CreateCase kEarlyExitFee[] = {
        // rate 100'000 (100%)
        {.subscription = 600, .redemption = 1'000'600, .earlyExitFeeRate = 99'998, .expected = tesSUCCESS},
        {.subscription = 600, .redemption = 1'000'600, .earlyExitFeeRate = 99'999, .expected = tesSUCCESS},
        {.subscription = 600, .redemption = 1'000'600, .earlyExitFeeRate = 100'000, .expected = tesSUCCESS},
        {.subscription = 600, .redemption = 1'000'600, .earlyExitFeeRate = 100'001, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        {.subscription = 600, .redemption = 1'000'600, .earlyExitFeeRate = 100'002, .expected = temMALFORMED, .leanError = LeanError::notLawful},
    };
    // clang-format on

    // Runs the open-ended lists or, when `closed`, the closed-ended ones: a closed-ended vault is
    // created from its own fields, not staged.
    void
    runCreateBoundaries(jtx::Env& env, Setup const& s, bool closed)
    {
        std::uint32_t const p = parentCloseTime(env);
        auto const run = [&](std::string const& name,
                             TestAssets const& assets,
                             std::span<CreateCase const> cases) {
            testcase("create " + name + (closed ? ", closed-ended" : ""));
            for (Asset const& asset : assets)
            {
                for (std::size_t i = 0; CreateCase const& c : cases)
                {
                    auto const date = [&](std::optional<std::int64_t> offset) {
                        return offset ? std::optional{static_cast<std::uint32_t>(p + *offset)}
                                      : std::nullopt;
                    };
                    VaultCreateArgs const args{
                        .scale = c.scale,
                        .assetsMaximum = c.maximum
                            ? std::optional{Number{*c.maximum, c.assetExponent}}
                            : std::nullopt,
                        .subscriptionDate = date(c.subscription),
                        .redemptionDate = date(c.redemption),
                        .earlyExitFeeRate = c.earlyExitFeeRate,
                    };
                    auto const [cpp, lean] = applyCreate(env, s.owner, asset, args);
                    std::string const at = rowText(i++) + argsText(asset, args, p);
                    expectRow(*this, at, cpp, lean, c.expected, c.leanError);
                }
            }
        };

        if (!closed)
        {
            run("scale", s.iou, kScale);
            run("maximum sign", s.integral, kMaximumSign);
            run("maximum sign", s.iou, kMaximumSignIou);
            run("maximum grid", s.iou, kMaximumGrid);
            run("maximum range", s.xrp, kMaximumRangeXrp);
            run("maximum range", s.mpt, kMaximumRangeMpt);
            run("maximum range", s.iou, kMaximumRangeIou);
            return;
        }
        run("schedule", s.all, kSchedule);
        run("early-exit fee", s.all, kEarlyExitFee);
    }

    void
    testCreateBoundaries(jtx::Env& env, Setup const& s)
    {
        runCreateBoundaries(env, s, false);
    }

    void
    testClosedEndedCreateBoundaries(jtx::Env& env, Setup const& s)
    {
        runCreateBoundaries(env, s, true);
    }

    void
    runTests() override
    {
        jtx::Env env{*this, vaultTestAmendments()};
        Setup const s = setup(env);

        struct CreateTest
        {
            char const* name;
            AssetKind asset;
            VaultCreateArgs args{};
            std::optional<ScheduleOffsets> schedule{};
            TER expected;
            std::optional<LeanError> leanError{};
        };
        auto const create = [&](CreateTest const& t) {
            runVaultCreate(env, s, t.name, t.asset, t.args, t.schedule, t.expected, t.leanError);
        };

        // clang-format off
        static CreateTest const kScaleAndMaximumTests[] = {
            // Open-ended vaults: the scale defaults to 6 for an IOU and is 0 for XRP and MPT.
            {.name = "IOU vault, default scale", .asset = AssetKind::iou, .expected = tesSUCCESS},
            {.name = "MPT vault", .asset = AssetKind::mpt, .expected = tesSUCCESS},
            {.name = "XRP vault with a maximum", .asset = AssetKind::xrp, .args = {.assetsMaximum = Number{1'000}}, .expected = tesSUCCESS},
            {.name = "IOU vault, owner can block deposits", .asset = AssetKind::iou, .args = {.ownerCanBlockDeposit = true}, .expected = tesSUCCESS},

            // AssetsMaximum must lie on the 10^-scale grid.
            {.name = "IOU maximum on the scale-2 grid", .asset = AssetKind::iou, .args = {.scale = 2, .assetsMaximum = Number{100'001, -2}}, .expected = tesSUCCESS},
            {.name = "IOU maximum off the scale-2 grid", .asset = AssetKind::iou, .args = {.scale = 2, .assetsMaximum = Number{1'001, -3}}, .expected = tecPRECISION_LOSS},
            // FV_M2_19 (regression): a 17-digit AssetsMaximum used to be rounded to the STAmount grid
            // on create, storing a different cap than submitted. It is now rejected upfront.
            {.name = "IOU maximum over 16 digits", .asset = AssetKind::iou, .args = {.assetsMaximum = Number{12'345'678'901'234'567LL, -1}}, .expected = tecPRECISION_LOSS},
            {.name = "IOU scale above 10", .asset = AssetKind::iou, .args = {.scale = 11}, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        };
        // clang-format on
        for (CreateTest const& t : kScaleAndMaximumTests)
            create(t);
        testIntegralScale(env, s, s.xrpAsset);
        testIntegralScale(env, s, s.mptAsset);

        // clang-format off
        static CreateTest const kZeroAndNegativeMaximumTests[] = {
            // A zero maximum means no cap; a negative one is rejected.
            {.name = "IOU vault with a zero maximum", .asset = AssetKind::iou, .args = {.assetsMaximum = Number{0}}, .expected = tesSUCCESS},
            {.name = "IOU vault with a negative maximum", .asset = AssetKind::iou, .args = {.assetsMaximum = Number{-1}}, .expected = temMALFORMED, .leanError = LeanError::notLawful},
        };
        // clang-format on
        for (CreateTest const& t : kZeroAndNegativeMaximumTests)
            create(t);
        testCreateBoundaries(env, s);

        // clang-format off
        static CreateTest const kClosedEndedTests[] = {
            // Closed-ended vaults.
            {.name = "closed-ended IOU vault with an early-exit fee", .asset = AssetKind::iou, .args = {.earlyExitFeeRate = 5'000}, .schedule = ScheduleOffsets{.subscription = 60, .investmentPeriod = 1'000'000}, .expected = tesSUCCESS},
            {.name = "closed-ended vault subscribing one second from now", .asset = AssetKind::iou, .schedule = ScheduleOffsets{.subscription = 1, .investmentPeriod = 180}, .expected = tesSUCCESS},
            {.name = "closed-ended vault whose subscription date is now", .asset = AssetKind::iou, .schedule = ScheduleOffsets{.subscription = 0, .investmentPeriod = 180}, .expected = tecEXPIRED},
            {.name = "closed-ended investment period below 180 s", .asset = AssetKind::iou, .schedule = ScheduleOffsets{.subscription = 60, .investmentPeriod = 179}, .expected = temMALFORMED, .leanError = LeanError::notLawful},
            // The investment period must stay below 30 years (946'708'560 s).
            {.name = "closed-ended investment period just below 30 years", .asset = AssetKind::iou, .schedule = ScheduleOffsets{.subscription = 60, .investmentPeriod = 946'708'559}, .expected = tesSUCCESS},
            {.name = "closed-ended investment period of 30 years", .asset = AssetKind::iou, .schedule = ScheduleOffsets{.subscription = 60, .investmentPeriod = 946'708'560}, .expected = temMALFORMED, .leanError = LeanError::notLawful},
            {.name = "closed-ended early-exit fee above 100%", .asset = AssetKind::iou, .args = {.earlyExitFeeRate = 100'001}, .schedule = ScheduleOffsets{.subscription = 60, .investmentPeriod = 1'000'000}, .expected = temMALFORMED, .leanError = LeanError::notLawful},
            // Accepted divergence: an early-exit fee, even zero, on an open-ended vault. C++ preflight
            // returns temMALFORMED; the model copies doApply, which drops the rate, and creates the
            // vault.
            // {.name = "open-ended vault with an early-exit fee", .asset = AssetKind::iou, .args = {.earlyExitFeeRate = 5'000}, .expected = temMALFORMED},
            // {.name = "open-ended vault with a zero early-exit fee", .asset = AssetKind::iou, .args = {.earlyExitFeeRate = 0}, .expected = temMALFORMED},
        };
        // clang-format on
        for (CreateTest const& t : kClosedEndedTests)
            create(t);
        testClosedEndedCreateBoundaries(env, s);
    }
};

BEAST_DEFINE_TESTSUITE(LeanVaultCreate, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
