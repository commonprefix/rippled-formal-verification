// Scratch suite (manual, not part of the formal_verification group): reproductions of the candidate
// model/C++ gaps from vault-lending-cusps.md and validation of its cusp values. Run with
// --unittest=LeanCuspScratch. Each check prints "cpp=... lean=..."; a failure is a disagreement.

#include <test/formal_verification/common/LeanSuite.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/ffi/vault/VaultClawbackFFI.h>
#include <test/formal_verification/ffi/vault/VaultCreateFFI.h>
#include <test/formal_verification/ffi/vault/VaultDepositFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/ffi/vault/VaultWithdrawFFI.h>
#include <test/formal_verification/tx/lending/LendingTestHelpers.h>
#include <test/formal_verification/tx/vault/DepositSweepCases.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/tx/apply.h>

#include <chrono>
#include <cstdint>
#include <limits>
#include <map>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

class LeanCuspScratch_test : public LeanSuite
{
    static std::string
    leanText(std::optional<LeanError> const& error, std::optional<TER> const& ter)
    {
        if (error)
            return "model error " + std::to_string(static_cast<int>(*error)) +
                (*error == LeanError::outOfRange      ? " (outOfRange)"
                     : *error == LeanError::notLawful ? " (notLawful)"
                     : *error == LeanError::overflow  ? " (overflow)"
                                                      : "");
        return transToken(ter.value_or(tesSUCCESS));
    }

    // Report both verdicts and expect them to agree (a model error counts as tefEXCEPTION).
    void
    report(
        std::string const& label,
        TER cpp,
        std::optional<LeanError> const& leanError,
        std::optional<TER> const& leanTer)
    {
        TER const lean = leanError ? TER{tefEXCEPTION} : leanTer.value_or(tesSUCCESS);
        log << "SCRATCH " << label << ": cpp=" << transToken(cpp)
            << " lean=" << leanText(leanError, leanTer) << std::endl;
        BEAST_EXPECTS(
            lean == cpp,
            label + ": cpp=" + transToken(cpp) + " lean=" + leanText(leanError, leanTer));
    }

    // Gap 1: an XRP withdraw by shares whose payout converts to more than 1e17 drops.
    void
    gapWithdrawSharesOutOfRange(std::int64_t shares)
    {
        using namespace jtx;
        testcase("gap: XRP withdraw by " + std::to_string(shares) + " shares");
        Env env(*this);
        Account const owner{"owner"};
        Account const holder{"holder"};
        env.fund(XRP(1'000'000), owner, holder);
        env.close();
        Keylet const vault = createVault(env, owner, xrpIssue());
        env(jtx::Vault::deposit({.depositor = holder, .id = vault.key, .amount = XRP(1)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        Vault const before = readVaultState(env, vault, xrpIssue());
        STAmount const amount{MPTIssue{env.le(vault)->at(sfShareMPTID)}, shares};
        LeanVaultResult const lean = leanVaultWithdraw(
            before,
            amount,
            true,
            parentCloseTime(env),
            holderOwnsAllShares(env, vault, holder),
            Number{fetchHolderShares(env, vault, holder)});
        env(jtx::Vault::withdraw({.depositor = holder, .id = vault.key, .amount = amount}),
            jtx::Ter(std::ignore));
        report(
            "withdraw " + std::to_string(shares) + " shares of 1e6 (NAV 1e6 drops)",
            env.ter(),
            lean.leanError,
            lean.error);
    }

    // Gap 2: clawing back more than one of two holders' shares are worth.
    void
    gapClawbackOverHolderValue(std::int64_t amount)
    {
        using namespace jtx;
        testcase("gap: clawback " + std::to_string(amount) + " from a holder worth 1000");
        Env env(*this);
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const alice{"alice"};
        Account const bob{"bob"};
        env.fund(XRP(1'000'000), owner, issuer, alice, bob);
        env.close();
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();
        PrettyAsset const iou = issuer["USD"];
        env.trust(iou(1'000'000), alice);
        env.trust(iou(1'000'000), bob);
        env(pay(issuer, alice, iou(10'000)));
        env(pay(issuer, bob, iou(10'000)));
        env.close();

        jtx::Vault v{env};
        auto [tx, vault] = v.create({.owner = owner, .asset = iou.raw()});
        tx[sfScale] = 0;
        env(tx);
        env.close();
        env(jtx::Vault::deposit({.depositor = alice, .id = vault.key, .amount = iou(1'000)}),
            jtx::Ter(tesSUCCESS));
        env(jtx::Vault::deposit({.depositor = bob, .id = vault.key, .amount = iou(1'000)}),
            jtx::Ter(tesSUCCESS));
        env.close();

        Vault const before = readVaultState(env, vault, iou.raw());
        STAmount const request = iou(amount);
        LeanVaultResult const lean = leanVaultClawback(
            before,
            request,
            fetchHolderShares(env, vault, alice),
            holderOwnsAllShares(env, vault, alice));
        env(jtx::Vault::clawback(
                {.issuer = issuer, .id = vault.key, .holder = alice, .amount = request}),
            jtx::Ter(std::ignore));
        report(
            "claw " + std::to_string(amount) + " from alice (1000 of 2000 shares)",
            env.ter(),
            lean.leanError,
            lean.error);
    }

    // Gap 3: an XRP vault created with an AssetsMaximum above 1e17 drops.
    void
    gapCreateXrpMaximum(Number const& maximum)
    {
        using namespace jtx;
        testcase("gap: create XRP vault with maximum " + to_string(maximum));
        Env env(*this);
        Account const owner{"owner"};
        env.fund(XRP(1'000'000), owner);
        env.close();

        VaultCreateArgs args{.assetsMaximum = maximum, .numericType = 0};
        LawfulTerResult const can = leanCanVaultCreate(args, parentCloseTime(env));
        LeanCreateResult const created = leanVaultCreate(args);
        jtx::Vault v{env};
        auto [tx, vault] = v.create({.owner = owner, .asset = xrpIssue()});
        tx[sfAssetsMaximum] = maximum;
        env(tx, jtx::Ter(std::ignore));
        TER const cpp = env.ter();
        std::optional<LeanError> const leanError =
            can.leanError ? can.leanError : created.leanError;
        // The create suite's convention: a preflight rejection must be a not-lawful vault.
        bool const agree =
            isTemMalformed(cpp) ? leanError == LeanError::notLawful : !leanError && can.ter == cpp;
        log << "SCRATCH create XRP maximum " << to_string(maximum) << ": cpp=" << transToken(cpp)
            << " lean canCreate=" << transToken(can.ter) << " create="
            << (created.leanError ? leanText(created.leanError, std::nullopt) : "lawful vault")
            << std::endl;
        BEAST_EXPECTS(
            agree, "create XRP maximum " + to_string(maximum) + ": cpp=" + transToken(cpp));
    }

    // Gap 4: a loan whose origination fee exceeds the principal.
    void
    gapLoanOriginationFee(Number const& fee)
    {
        using namespace jtx;
        testcase("gap: LoanSet origination fee " + to_string(fee) + " on principal 1000");
        Env env(*this);
        auto const f = setUpBrokerVault(
            env,
            BrokerConfig{.coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt},
            Number{10'000});
        depositCover(env, f, Number{500});
        LoanParams const p{.principal = Number{1'000}, .originationFee = fee};

        LoanBroker const broker = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LoanSetArgs const args = loanSetArgs(p);
        std::uint32_t const closeTime = ledgerCloseTime(env);
        LawfulTerResult const can =
            leanCanLoanCreate(broker, pool, args, closeTime, parentCloseTime(env));
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS && !can.leanError)
            result =
                leanLoanCreate(broker, pool, args, closeTime, loanTemplate(broker, p, closeTime));
        env(loanSetTx(f, p),
            Sig(sfCounterpartySignature, f.owner),
            Fee(env.current()->fees().base * 2),
            jtx::Ter(std::ignore));
        TER const cpp = env.ter();
        std::optional<LeanError> const leanError =
            can.leanError ? can.leanError : (result ? result->leanError : std::nullopt);
        TER const lean =
            modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        report("LoanSet fee " + to_string(fee) + " principal 1000", cpp, leanError, lean);
    }

    // Output check (both sides model it): a 1-drop deposit into S = k * T - 1 shares, T = 4e15
    // drops. The catalogue predicts k - 1 shares for k <= 1000 and k (rounded up) from k = 1001.
    void
    checkShareQuotientRoundUp(std::int64_t k)
    {
        using namespace jtx;
        testcase("output: share quotient round-up at k = " + std::to_string(k));
        Env env(*this);
        Account const owner{"owner"};
        Account const depositor{"depositor"};
        env.fund(XRP(1'000'000), owner);
        env.fund(XRP(9'500'000'000), depositor);
        env.close();
        Keylet const vault = createSweepVault(env, owner, depositor, xrpIssue());
        std::int64_t const total = 4'000'000'000'000'000;
        std::int64_t const shares = k * total - 1;
        StagedVault const staged{
            .available = gridUnits(env, vault, total),
            .sharesTotal = static_cast<std::uint64_t>(shares)};
        STAmount const amount = gridUnits(env, vault, 1);
        AppliedDeposit const cpp = applyDeposit(env, vault, depositor, staged, amount);
        LeanVaultResult const lean = leanVaultDeposit(cpp.pre, amount, false, parentCloseTime(env));
        Number const cppMinted = cpp.post.sharesTotal - cpp.pre.sharesTotal;
        Number const leanMinted = lean.vault.sharesTotal - cpp.pre.sharesTotal;
        log << "SCRATCH share quotient k=" << k << ": cpp=" << transToken(cpp.ter) << " minted "
            << to_string(cppMinted) << ", lean=" << leanText(lean.leanError, lean.error)
            << " minted " << to_string(leanMinted) << std::endl;
        report("share quotient k=" + std::to_string(k), cpp.ter, lean.leanError, lean.error);
        if (cpp.ter == tesSUCCESS && !lean.leanError && !lean.error)
            BEAST_EXPECTS(cppMinted == leanMinted, "minted shares differ");
    }

    // ---- Cusp validation ------------------------------------------------------------------------

    // One sample's verdicts on both sides.
    struct Outcome
    {
        TER cpp;
        TER lean;
        std::string text;
    };

    // One line per row: verdict counts, disagreements, and whether the moved values crossed.
    void
    summarize(
        std::string const& name,
        std::string const& row,
        std::vector<Outcome> const& outcomes,
        bool mustCross = true)
    {
        std::map<std::string, int> counts;
        int disagreements = 0;
        std::string firstDisagreement;
        for (Outcome const& o : outcomes)
        {
            ++counts[transToken(o.cpp)];
            if (o.cpp != o.lean)
            {
                if (disagreements++ == 0)
                    firstDisagreement = o.text;
            }
        }
        std::string verdicts;
        for (auto const& [ter, n] : counts)
            verdicts += ter + " x" + std::to_string(n) + " ";
        bool const crossed = counts.size() > 1;
        log << "ROW " << name << " | " << row << " | " << verdicts << "| disagree " << disagreements
            << (disagreements ? " (first: " + firstDisagreement + ")" : "") << " | crossed "
            << (crossed ? "yes" : "no") << std::endl;
        BEAST_EXPECTS(
            disagreements == 0, name + " " + row + ": first disagreement " + firstDisagreement);
        if (mustCross)
            BEAST_EXPECTS(crossed, name + " " + row + ": never crossed, always " + verdicts);
    }

    // Vault fields to stage, in grid units; dates make the vault closed-ended.
    struct Stage
    {
        std::int64_t available = 0;
        std::int64_t deployed = 0;
        std::int64_t loss = 0;
        std::int64_t sharesTotal = 0;
        std::optional<std::int64_t> holderShares;  // defaults to sharesTotal
        std::optional<std::uint32_t> subscriptionDate;
        std::optional<std::uint32_t> redemptionDate;
        std::optional<std::uint32_t> feeRate;
    };

    static std::string
    stageText(Stage const& s)
    {
        std::string t = "avail " + std::to_string(s.available) + " depl " +
            std::to_string(s.deployed) + " S " + std::to_string(s.sharesTotal) + " H " +
            std::to_string(s.holderShares.value_or(s.sharesTotal));
        if (s.subscriptionDate)
            t += " sub " + std::to_string(*s.subscriptionDate) + " red " +
                std::to_string(*s.redemptionDate);
        if (s.feeRate)
            t += " fee " + std::to_string(*s.feeRate);
        return t;
    }

    // Stage `s` on `view`: vault totals, phase fields, shares outstanding, the holder's shares and
    // the pseudo-account's real holding of the asset (equal to the available assets).
    static void
    stageView(
        OpenView& view,
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Stage const& s)
    {
        Sandbox sb(&view, TapNone);
        auto v = sb.peek(vault);
        Asset const asset = v->at(sfAsset);
        auto const units = [&](std::int64_t n) { return Number{gridUnits(env, vault, n)}; };
        v->at(sfAssetsAvailable) = units(s.available);
        v->at(sfAssetsDeployed) = units(s.deployed);
        v->at(sfLossUnrealized) = units(s.loss);
        {
            NumberRoundModeGuard const rg(Number::RoundingMode::Downward);
            v->at(sfAssetsTotal) = STAmount{asset, getAssetsTotal(v)};
        }
        if (s.subscriptionDate)
        {
            v->at(sfVaultKind) = std::to_underlying(VaultKind::ClosedEnded);
            v->at(sfSubscriptionDate) = *s.subscriptionDate;
            v->at(sfRedemptionDate) = *s.redemptionDate;
        }
        if (s.feeRate)
            v->at(sfEarlyExitFeeRate) = *s.feeRate;
        auto const shareId = v->at(sfShareMPTID);
        auto issuance = sb.peek(keylet::mptokenIssuance(shareId));
        issuance->setFieldU64(sfOutstandingAmount, static_cast<std::uint64_t>(s.sharesTotal));
        auto token = sb.peek(keylet::mptoken(shareId, holder.id()));
        token->setFieldU64(
            sfMPTAmount, static_cast<std::uint64_t>(s.holderShares.value_or(s.sharesTotal)));
        AccountID const pseudo = v->at(sfAccount);
        STAmount const held = gridUnits(env, vault, s.available);
        if (asset.native())
        {
            auto acct = sb.peek(keylet::account(pseudo));
            acct->setFieldAmount(sfBalance, held);
            sb.update(acct);
        }
        else if (asset.holds<MPTIssue>())
        {
            auto mpt = sb.peek(keylet::mptoken(asset.get<MPTIssue>().getMptID(), pseudo));
            mpt->setFieldU64(sfMPTAmount, static_cast<std::uint64_t>(s.available));
            sb.update(mpt);
        }
        else
        {
            Issue const issue = asset.get<Issue>();
            auto line = sb.peek(keylet::trustLine(pseudo, issue));
            STAmount balance{Issue{issue.currency, noAccount()}, Number{held}};
            if (pseudo > issue.account)
                balance.negate();
            line->setFieldAmount(sfBalance, balance);
            sb.update(line);
        }
        sb.update(v);
        sb.update(issuance);
        sb.update(token);
        sb.apply(view);
    }

    struct Applied
    {
        Vault pre;
        TER ter;
        Vault post;
    };

    // Stage `s`, then apply `tx` (signed by env.jt) on a throwaway copy of the open ledger.
    static Applied
    applyStaged(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Stage const& s,
        json::Value const& tx)
    {
        OpenView view{*env.current()};
        stageView(view, env, vault, holder, s);
        Asset const asset = view.read(vault)->at(sfAsset);
        Vault const pre = readVaultState(view, vault, asset);
        auto const jt = env.jt(tx);
        TER const ter = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
        return {.pre = pre, .ter = ter, .post = readVaultState(view, vault, asset)};
    }

    static TER
    leanVerdict(std::optional<LeanError> const& error, std::optional<TER> const& ter)
    {
        return error ? TER{tefEXCEPTION} : ter.value_or(tesSUCCESS);
    }

    // Both succeeded: the post-states must agree as well.
    static std::string
    postStateDiff(Vault const& lean, Vault const& cpp)
    {
        std::string d;
        auto const field = [&](char const* n, Number const& l, Number const& c) {
            if (l != c)
                d += std::string(" ") + n + " lean=" + to_string(l) + " cpp=" + to_string(c);
        };
        field("total", lean.assetsTotal, cpp.assetsTotal);
        field("available", lean.assetsAvailable, cpp.assetsAvailable);
        field("shares", lean.sharesTotal, cpp.sharesTotal);
        field("loss", lean.lossUnrealized, cpp.lossUnrealized);
        return d;
    }

    // A staged deposit of `amount` units (or a donation) on both sides.
    Outcome
    stagedDeposit(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& depositor,
        Stage const& s,
        std::int64_t amount,
        bool donate = false)
    {
        STAmount const a = gridUnits(env, vault, amount);
        jtx::Vault::DepositArgs args{.depositor = depositor, .id = vault.key, .amount = a};
        if (donate)
            args.flags = tfVaultDonate;
        Applied const cpp = applyStaged(env, vault, depositor, s, jtx::Vault::deposit(args));
        LeanVaultResult const lean = leanVaultDeposit(cpp.pre, a, donate, parentCloseTime(env));
        TER lean_ter = leanVerdict(lean.leanError, lean.error);
        std::string text = stageText(s) + " amount " + std::to_string(amount) +
            " cpp=" + transToken(cpp.ter) + " lean=" + leanText(lean.leanError, lean.error);
        if (cpp.ter == tesSUCCESS && lean_ter == tesSUCCESS)
        {
            std::string const d = postStateDiff(lean.vault, cpp.post);
            if (!d.empty())
            {
                lean_ter = tefINTERNAL;  // mark the post-state mismatch as a disagreement
                text += d;
            }
        }
        return {.cpp = cpp.ter, .lean = lean_ter, .text = text};
    }

    // A staged withdraw by assets or by shares on both sides.
    Outcome
    stagedWithdraw(
        jtx::Env& env,
        Keylet const& vault,
        jtx::Account const& holder,
        Stage const& s,
        std::int64_t amount,
        bool byShares)
    {
        STAmount const a = byShares ? STAmount{MPTIssue{env.le(vault)->at(sfShareMPTID)}, amount}
                                    : gridUnits(env, vault, amount);
        Applied const cpp = applyStaged(
            env,
            vault,
            holder,
            s,
            jtx::Vault::withdraw({.depositor = holder, .id = vault.key, .amount = a}));
        std::int64_t const h = s.holderShares.value_or(s.sharesTotal);
        LeanVaultResult const lean = leanVaultWithdraw(
            cpp.pre, a, byShares, parentCloseTime(env), h == s.sharesTotal, Number{h});
        TER lean_ter = leanVerdict(lean.leanError, lean.error);
        std::string text = stageText(s) + (byShares ? " shares " : " assets ") +
            std::to_string(amount) + " cpp=" + transToken(cpp.ter) +
            " lean=" + leanText(lean.leanError, lean.error);
        if (cpp.ter == tesSUCCESS && lean_ter == tesSUCCESS)
        {
            std::string d = postStateDiff(lean.vault, cpp.post);
            Number const cppPayout = cpp.pre.assetsAvailable - cpp.post.assetsAvailable;
            if (Number{lean.assets} != cppPayout)
                d += " payout lean=" + to_string(Number{lean.assets}) +
                    " cpp=" + to_string(cppPayout);
            if (!d.empty())
            {
                lean_ter = tefINTERNAL;
                text += d;
            }
        }
        return {.cpp = cpp.ter, .lean = lean_ter, .text = text};
    }

    struct ScratchVaults
    {
        std::vector<std::tuple<std::string, Keylet, jtx::Account>> all;
    };

    // One ledger with a vault per asset (IOU at scales 0, 6, 10), like the deposit sweeps.
    ScratchVaults
    makeVaults(jtx::Env& env)
    {
        using namespace jtx;
        Account const owner{"owner"};
        Account const issuer{"issuer"};
        Account const depositor{"depositor"};
        env.fund(XRP(1'000'000), owner, issuer);
        env.fund(XRP(9'500'000'000), depositor);
        // Staged dates sit up to 1e6 s before the parent close time, which starts near 0.
        env.close(env.now() + std::chrono::seconds{100'000'000});
        PrettyAsset const xrp = xrpIssue();
        PrettyAsset const iou = issuer["USD"];
        MPTTester mptt{env, issuer, kMptInitNoFund};
        mptt.create({.flags = tfMPTCanTransfer});
        mptt.authorize({.account = depositor});
        PrettyAsset const mpt = mptt.issuanceID();
        env(pay(issuer, depositor, mpt(9'200'000'000'000'000)));
        env.close();
        ScratchVaults v;
        auto const add =
            [&](Account const& who, PrettyAsset const& a, std::optional<std::uint8_t> scale) {
                Keylet const k = createSweepVault(env, owner, who, a, scale);
                v.all.emplace_back(vaultName(env, k), k, who);
            };
        add(depositor, xrp, std::nullopt);
        add(depositor, mpt, std::nullopt);
        add(issuer, iou, 0);
        add(issuer, iou, 6);
        add(issuer, iou, 10);
        return v;
    }

    // Deposit 1.2: a plain deposit after the subscription date is tecEXPIRED (P <= sub is still
    // Subscription). Rows put the subscription date at P + d.
    void
    validateDepositSubscription(jtx::Env& env, ScratchVaults const& vaults)
    {
        std::uint32_t const p = parentCloseTime(env);
        for (auto const& [name, vault, who] : vaults.all)
        {
            testcase("validate deposit subscription date " + name);
            std::vector<Outcome> out;
            for (std::int64_t const d : kAroundCusp)
            {
                Stage const s{
                    .available = 1'000,
                    .sharesTotal = 1'000,
                    .subscriptionDate = static_cast<std::uint32_t>(p + d),
                    .redemptionDate = static_cast<std::uint32_t>(p + d + 1'000'000)};
                out.push_back(stagedDeposit(env, vault, who, s, 10));
            }
            summarize("deposit subscription " + name, "sub = P + d", out);
        }
    }

    // Deposit 1.3: an insolvent vault (assets total 0, shares outstanding) is locked.
    void
    validateDepositInsolvent(jtx::Env& env, ScratchVaults const& vaults)
    {
        for (auto const& [name, vault, who] : vaults.all)
        {
            testcase("validate deposit insolvent lock " + name);
            for (std::int64_t const shares : {std::int64_t{1}, kOrdinaryUnits, kLargeUnits})
            {
                std::vector<Outcome> out;
                for (std::int64_t const d : kAroundCusp)
                {
                    if (d < 0)
                        continue;
                    Stage const s{.available = d, .sharesTotal = shares};
                    out.push_back(stagedDeposit(env, vault, who, s, 1));
                }
                summarize(
                    "deposit insolvent " + name,
                    "S " + std::to_string(shares) + ", total 0..2",
                    out);
            }
        }
    }

    // Deposit 1.5: the charge rounding table on the IOU vaults (both sides succeed; post-states
    // compared).
    void
    validateIouChargeRounding(jtx::Env& env, ScratchVaults const& vaults)
    {
        for (auto const& [name, vault, who] : vaults.all)
        {
            if (name.rfind("IOU", 0) != 0)
                continue;
            testcase("validate charge rounding " + name);
            for (auto const& [cusp, cases] : kChargeRoundingCases)
            {
                std::vector<Outcome> out;
                for (PriceCusp const& c : cases)
                {
                    Stage const st{.available = c.total, .sharesTotal = c.sharesTotal};
                    out.push_back(stagedDeposit(env, vault, who, st, c.amount));
                }
                summarize("charge rounding " + name, describe(cusp), out, false);
            }
        }
    }

    // Withdraw 2.1: without a fee field the Investment phase is tecTOO_SOON; Subscription runs to
    // P = sub inclusive, Redemption starts at P = red.
    void
    validateWithdrawPhase(
        jtx::Env& env,
        ScratchVaults const& vaults,
        std::optional<std::uint32_t> fee)
    {
        std::uint32_t const p = parentCloseTime(env);
        std::string const feeText = fee ? " fee " + std::to_string(*fee) : " no fee";
        for (auto const& [name, vault, who] : vaults.all)
        {
            testcase("validate withdraw phase " + name + feeText);
            std::vector<Outcome> subscription;
            std::vector<Outcome> redemption;
            for (std::int64_t const d : kAroundCusp)
            {
                Stage s{.available = 1'000, .sharesTotal = 1'000, .feeRate = fee};
                s.subscriptionDate = static_cast<std::uint32_t>(p + d);
                s.redemptionDate = static_cast<std::uint32_t>(p + d + 1'000'000);
                subscription.push_back(stagedWithdraw(env, vault, who, s, 400, false));
                s.subscriptionDate = static_cast<std::uint32_t>(p + d - 1'000'000);
                s.redemptionDate = static_cast<std::uint32_t>(p + d);
                redemption.push_back(stagedWithdraw(env, vault, who, s, 400, false));
            }
            // With a fee field Investment is open, so only the payout changes (no crossing).
            summarize("withdraw phase" + feeText + " " + name, "sub = P + d", subscription, !fee);
            summarize("withdraw phase" + feeText + " " + name, "red = P + d", redemption, !fee);
        }
    }

    // Withdraw 2.3: by assets, trunc-up shares S*A/NAV; zero shares refused. Reuses the deposit
    // zero-shares rows, sole holder.
    void
    validateWithdrawZeroShares(jtx::Env& env, ScratchVaults const& vaults)
    {
        for (auto const& [name, vault, who] : vaults.all)
        {
            testcase("validate withdraw zero shares " + name);
            for (auto const& [cusp, cases] : kZeroSharesCases)
            {
                std::vector<Outcome> out;
                for (PriceCusp const& c : cases)
                {
                    if (c.amount > c.total)
                        continue;
                    Stage const s{.available = c.total, .sharesTotal = c.sharesTotal};
                    out.push_back(stagedWithdraw(env, vault, who, s, c.amount, false));
                }
                summarize("withdraw zero shares " + name, describe(cusp), out, false);
            }
        }
    }

    // Withdraw 2.7: with assets deployed, a withdrawal above the available assets is
    // tecINSUFFICIENT_FUNDS. Rows withdraw exactly the available assets.
    void
    validateWithdrawAvailable(jtx::Env& env, ScratchVaults const& vaults)
    {
        struct Row
        {
            std::int64_t available;
            std::int64_t deployed;
        };
        Row const rows[] = {
            {3, 1},
            {kOrdinaryUnits, 1},
            {kOrdinaryUnits, kOrdinaryUnits},
            {3, kOrdinaryUnits},
            {kLargeUnits, kLargeUnits}};
        for (auto const& [name, vault, who] : vaults.all)
        {
            testcase("validate withdraw available " + name);
            for (Row const& r : rows)
            {
                std::vector<Outcome> out;
                for (std::int64_t const dA : kAroundCusp)
                {
                    for (std::int64_t const dAvail : kAroundCusp)
                    {
                        std::int64_t const avail = r.available + dAvail;
                        std::int64_t const total = avail + r.deployed;
                        Stage const s{
                            .available = avail, .deployed = r.deployed, .sharesTotal = total};
                        out.push_back(stagedWithdraw(env, vault, who, s, r.available + dA, false));
                    }
                }
                summarize(
                    "withdraw available " + name,
                    "avail " + std::to_string(r.available) + " depl " + std::to_string(r.deployed),
                    out);
            }
        }
    }

    // Withdraw 2.9 / 2.11: in Investment with an early-exit fee rate r, the net payout
    // x * (1e5 - r) / 1e5 must be at least one unit (tecPRECISION_LOSS) and at most the
    // available assets (tecINSUFFICIENT_FUNDS).
    void
    validateWithdrawFee(jtx::Env& env, ScratchVaults const& vaults)
    {
        std::uint32_t const p = parentCloseTime(env);
        struct Row
        {
            std::uint32_t rate;
            std::int64_t x;
        };
        // x * (1e5 - rate) == 1e5: the smallest gross amount that pays one unit.
        Row const rows[] = {{50'000, 2}, {90'000, 10}, {99'000, 100}, {99'999, 100'000}};
        for (auto const& [name, vault, who] : vaults.all)
        {
            testcase("validate withdraw fee " + name);
            for (Row const& r : rows)
            {
                std::vector<Outcome> out;
                for (std::int64_t const dX : kAroundCusp)
                {
                    for (std::int64_t const dRate : kAroundCusp)
                    {
                        if (r.x + dX < 1 || r.rate + dRate > 100'000)
                            continue;  // not a withdrawal, or past the 100% fee maximum
                        Stage const s{
                            .available = 1'000'000,
                            .sharesTotal = 1'000'000,
                            .subscriptionDate = p - 1'000,
                            .redemptionDate = p + 1'000'000,
                            .feeRate = static_cast<std::uint32_t>(r.rate + dRate)};
                        out.push_back(stagedWithdraw(env, vault, who, s, r.x + dX, false));
                    }
                }
                summarize(
                    "withdraw fee consumes payout " + name,
                    "rate " + std::to_string(r.rate) + " x " + std::to_string(r.x),
                    out);
            }
        }
    }

    // Withdraw 2.12: redeeming every share (sh = S) with nothing deployed pays all available
    // assets; with assets deployed it is refused.
    void
    validateWithdrawFinal(jtx::Env& env, ScratchVaults const& vaults)
    {
        for (auto const& [name, vault, who] : vaults.all)
        {
            testcase("validate withdraw final " + name);
            for (std::int64_t const shares : {std::int64_t{2}, kOrdinaryUnits, kLargeUnits})
            {
                std::vector<Outcome> out;
                for (std::int64_t const dSh : kAroundCusp)
                {
                    for (std::int64_t const deployed : {0, 1, 2})
                    {
                        if (shares + dSh < 1 || dSh > 0)
                            continue;
                        Stage const s{
                            .available = shares,
                            .deployed = deployed,
                            .sharesTotal = shares + deployed};
                        out.push_back(
                            stagedWithdraw(env, vault, who, s, shares + deployed + dSh, true));
                    }
                }
                summarize("withdraw final " + name, "S " + std::to_string(shares), out);
            }
        }
    }

    // ---- Lending ----

    // A one-step LoanSet applied on a throwaway view of the fixture, and the model on the same
    // pre-state.
    Outcome
    stagedLoanSet(jtx::Env& env, BrokerFixture const& f, LoanParams const& p)
    {
        using namespace jtx;
        LoanBroker const broker = readLoanBrokerState(env, f.brokerKeylet, f.asset.raw());
        Vault const pool = readVaultState(env, f.vaultKeylet, f.asset.raw());
        LoanSetArgs const args = loanSetArgs(p);
        std::uint32_t const closeTime = ledgerCloseTime(env);
        LawfulTerResult const can =
            leanCanLoanCreate(broker, pool, args, closeTime, parentCloseTime(env));
        std::optional<LeanLoanResult> result;
        if (can.ter == tesSUCCESS && !can.leanError)
            result =
                leanLoanCreate(broker, pool, args, closeTime, loanTemplate(broker, p, closeTime));
        OpenView view{*env.current()};
        auto const jt = env.jt(
            loanSetTx(f, p),
            Sig(sfCounterpartySignature, f.owner),
            Fee(env.current()->fees().base * 2));
        TER const cpp = xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
        std::optional<LeanError> const leanError =
            can.leanError ? can.leanError : (result ? result->leanError : std::nullopt);
        TER const lean = leanError
            ? TER{tefEXCEPTION}
            : modelVerdict(can, result && !result->leanError ? result->error : std::nullopt);
        return {
            .cpp = cpp,
            .lean = lean,
            .text = "P " + to_string(p.principal) + " N " + std::to_string(p.paymentTotal) +
                " cpp=" + transToken(cpp) + " lean=" + transToken(lean)};
    }

    // LoanSet S7: with zero interest the loan passes iff P > (N - 1) * ceil(P / N).
    void
    validatePaymentCountGuard(LendingAsset kind)
    {
        using namespace jtx;
        std::string const asset = kind == LendingAsset::mpt ? "MPT" : "IOU";
        testcase("validate LoanSet payment-count guard " + asset);
        Env env(*this);
        auto const f = setUpBrokerVault(
            env,
            BrokerConfig{.coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt},
            Number{9'000'000'000},
            false,
            true,
            kind,
            std::chrono::seconds{200'000'000});
        struct Row
        {
            std::uint32_t n;
            std::int64_t p;
        };
        Row const rows[] = {
            {2, 2},
            {3, 3},
            {3, 5},
            {100, 100},
            {100, 4'951},
            {100, 5'000},
            {100, 9'802},
            {31'623, 999'950'885}};
        for (Row const& r : rows)
        {
            std::vector<Outcome> out;
            for (std::int64_t const dP : kAroundCusp)
            {
                for (std::int64_t const dN : kAroundCusp)
                {
                    if (r.p + dP < 1 || r.n + dN < 1)
                        continue;
                    LoanParams const p{
                        .principal = Number{r.p + dP},
                        .paymentInterval = 60,
                        .paymentTotal = static_cast<std::uint32_t>(r.n + dN)};
                    out.push_back(stagedLoanSet(env, f, p));
                }
            }
            summarize(
                "LoanSet payment-count guard " + asset,
                "N " + std::to_string(r.n) + " P " + std::to_string(r.p),
                out);
        }
    }

    // LoanSet S9: a principal past the broker's debt maximum is tecLIMIT_EXCEEDED (no debt yet,
    // so the row is P == DM).
    void
    validateDebtMaximum()
    {
        using namespace jtx;
        for (std::int64_t const dm :
             {std::int64_t{2}, std::int64_t{1'000}, std::int64_t{1'000'000'000}})
        {
            testcase("validate LoanSet debt maximum " + std::to_string(dm));
            Env env(*this);
            auto const f = setUpBrokerVault(
                env,
                BrokerConfig{
                    .debtMaximum = Number{dm},
                    .coverRateMinimum = std::nullopt,
                    .coverRateLiquidation = std::nullopt},
                Number{9'000'000'000});
            std::vector<Outcome> out;
            for (std::int64_t const dP : kAroundCusp)
            {
                if (dm + dP < 1)
                    continue;
                out.push_back(stagedLoanSet(
                    env, f, LoanParams{.principal = Number{dm + dP}, .paymentTotal = 1}));
            }
            summarize("LoanSet debt maximum", "DM " + std::to_string(dm), out);
        }
    }

    // LoanSet S10: the broker's cover must reach ceil(P * r / 1e5).
    void
    validateCoverMinimum()
    {
        using namespace jtx;
        struct Row
        {
            std::int64_t p;
            std::uint32_t rate;
            std::int64_t cover;
        };
        Row const rows[] = {
            {100'000, 1, 1},
            {1'000'000'000, 10'000, 100'000'000},
            {1'000'000'001, 10'000, 100'000'001}};
        for (Row const& r : rows)
        {
            testcase("validate LoanSet cover minimum P " + std::to_string(r.p));
            for (std::int64_t const dC : kAroundCusp)
            {
                if (r.cover + dC < 1)
                    continue;
                Env env(*this);
                auto const f = setUpBrokerVault(
                    env, BrokerConfig{.coverRateMinimum = r.rate}, Number{9'000'000'000});
                depositCover(env, f, Number{r.cover + dC});
                std::vector<Outcome> out;
                for (std::int64_t const dP : kAroundCusp)
                    out.push_back(stagedLoanSet(
                        env, f, LoanParams{.principal = Number{r.p + dP}, .paymentTotal = 1}));
                summarize(
                    "LoanSet cover minimum",
                    "P " + std::to_string(r.p) + " r " + std::to_string(r.rate) + " C " +
                        std::to_string(r.cover + dC),
                    out,
                    false);
            }
        }
    }

    // LoanSet S5: a principal above the vault's available assets is tecINSUFFICIENT_FUNDS.
    void
    validateLoanAvailable()
    {
        using namespace jtx;
        for (std::int64_t const avail : {std::int64_t{2}, std::int64_t{1'000'000'000}})
        {
            testcase("validate LoanSet assets available " + std::to_string(avail));
            Env env(*this);
            auto const f = setUpBrokerVault(
                env,
                BrokerConfig{
                    .coverRateMinimum = std::nullopt, .coverRateLiquidation = std::nullopt},
                Number{avail});
            std::vector<Outcome> out;
            for (std::int64_t const dP : kAroundCusp)
            {
                if (avail + dP < 1)
                    continue;
                out.push_back(stagedLoanSet(
                    env, f, LoanParams{.principal = Number{avail + dP}, .paymentTotal = 1}));
            }
            summarize("LoanSet assets available", "avail " + std::to_string(avail), out);
        }
    }

    void
    runTests() override
    {
        constexpr std::int64_t kInt64Max = std::numeric_limits<std::int64_t>::max();
        // Payout = shares drops here: <= 1e17 is in range, above it STAmount throws.
        gapWithdrawSharesOutOfRange(100'000'000'000'000'000);
        gapWithdrawSharesOutOfRange(100'000'000'000'000'001);
        gapWithdrawSharesOutOfRange(200'000'000'000'000'000);
        gapWithdrawSharesOutOfRange(kInt64Max);

        gapClawbackOverHolderValue(1'000);
        gapClawbackOverHolderValue(1'001);
        gapClawbackOverHolderValue(1'500);

        gapCreateXrpMaximum(Number{100'000'000'000'000'000});
        gapCreateXrpMaximum(Number{100'000'000'000'000'001});
        gapCreateXrpMaximum(Number{200'000'000'000'000'000});

        gapLoanOriginationFee(Number{1'000});
        gapLoanOriginationFee(Number{1'001});

        for (std::int64_t const k : {1'000, 1'001, 2'000, 2'305})
            checkShareQuotientRoundUp(k);

        {
            jtx::Env env(*this);
            ScratchVaults const vaults = makeVaults(env);
            validateDepositSubscription(env, vaults);
            validateDepositInsolvent(env, vaults);
            validateIouChargeRounding(env, vaults);
            validateWithdrawPhase(env, vaults, std::nullopt);
            validateWithdrawPhase(env, vaults, 5'000);
            validateWithdrawZeroShares(env, vaults);
            validateWithdrawAvailable(env, vaults);
            validateWithdrawFee(env, vaults);
            validateWithdrawFinal(env, vaults);
        }
        validatePaymentCountGuard(LendingAsset::iou);
        validatePaymentCountGuard(LendingAsset::mpt);
        validateDebtMaximum();
        validateCoverMinimum();
        validateLoanAvailable();
    }
};

BEAST_DEFINE_TESTSUITE_MANUAL(LeanCuspScratch, formal_verification, xrpl);

}  // namespace xrpl::test::formal_verification
