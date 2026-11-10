#pragma once

#include <test/formal_verification/ffi/lending/LoanBrokerFFI.h>
#include <test/formal_verification/ffi/lending/LoanFFI.h>
#include <test/formal_verification/ffi/vault/VaultFFI.h>
#include <test/formal_verification/tx/vault/VaultTestHelpers.h>
#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/amount.h>
#include <test/jtx/fee.h>
#include <test/jtx/flags.h>
#include <test/jtx/mpt.h>
#include <test/jtx/pay.h>
#include <test/jtx/seq.h>
#include <test/jtx/sig.h>
#include <test/jtx/ter.h>
#include <test/jtx/trust.h>
#include <test/jtx/vault.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/beast/unit_test/suite.h>
#include <xrpl/ledger/OpenView.h>
#include <xrpl/ledger/Sandbox.h>
#include <xrpl/ledger/helpers/VaultHelpers.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/MPTIssue.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/STAmount.h>
#include <xrpl/protocol/STNumber.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/TER.h>
#include <xrpl/protocol/TxFlags.h>
#include <xrpl/tx/apply.h>

#include <chrono>
#include <cstdint>
#include <initializer_list>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>

namespace xrpl::test::formal_verification {

// Snapshot the loan broker on `view` into the model's LoanBroker DTO.
[[nodiscard]] inline LoanBroker
readBroker(ReadView const& view, Keylet const& brokerKeylet, Asset const& asset)
{
    auto const sle = view.read(brokerKeylet);
    if (!sle)
        throw std::runtime_error("readBroker: no loan broker on the view");
    return LoanBroker{
        .numericType = NumericTypeFFI::tagOf(asset),
        .managementFeeRate = sle->at(sfManagementFeeRate),
        .coverRateMinimum = sle->at(sfCoverRateMinimum),
        .coverRateLiquidation = sle->at(sfCoverRateLiquidation),
        .debtTotal = sle->at(sfDebtTotal),
        .debtMaximum = sle->at(sfDebtMaximum),
        .coverAvailable = sle->at(sfCoverAvailable),
        .loanCount = sle->at(sfOwnerCount)};
}

// A closed-ended IOU vault owned by `owner` with its loan broker. The holder is the vault's
// lender, the owner funds the broker cover, the borrower takes loans.
enum class LendingAsset : std::uint8_t { iou, mpt };

struct BrokerFixture
{
    jtx::Account owner;
    jtx::Account issuer;
    jtx::Account holder;
    jtx::Account borrower;
    jtx::PrettyAsset asset;
    Keylet vaultKeylet;
    Keylet brokerKeylet;
    NetClock::time_point subscriptionDate;
    NetClock::time_point redemptionDate;
};

// The loan broker's configurable fields, defaulting to a broker with a 10% minimum cover.
struct BrokerConfig
{
    std::optional<Number> debtMaximum;
    std::optional<std::uint16_t> managementFeeRate = 1'000;  // 1%
    std::optional<std::uint32_t> coverRateMinimum = 10'000;  // 10%
    std::optional<std::uint32_t> coverRateLiquidation = 20'000;
};

inline constexpr auto kBrokerSubscriptionOffset = std::chrono::seconds{600};
inline constexpr auto kBrokerInvestmentWindow = std::chrono::seconds{1'000'000};

// Fund the accounts and create the closed-ended vault, seeded by the holder during Subscription.
// The broker is created when `config` is set; `openEnded` creates a vault without a schedule
// (then no broker). The vault stays in Subscription unless `toInvestment`.
inline BrokerFixture
setUpBrokerVault(
    jtx::Env& env,
    std::optional<BrokerConfig> const& config,
    Number const& seed = Number{10'000},
    bool openEnded = false,
    bool toInvestment = true,
    LendingAsset assetKind = LendingAsset::iou,
    std::chrono::seconds investmentWindow = kBrokerInvestmentWindow)
{
    using namespace jtx;
    using namespace std::chrono_literals;
    Account const owner{"owner"};
    Account const issuer{"issuer"};
    Account const holder{"holder"};
    Account const borrower{"borrower"};
    env.fund(XRP(1'000'000), owner, issuer, holder, borrower);
    env.close();

    PrettyAsset const asset = [&] {
        if (assetKind == LendingAsset::mpt)
        {
            MPTTester mptt{env, issuer, kMptInitNoFund};
            mptt.create({.flags = tfMPTCanTransfer | tfMPTCanClawback});
            PrettyAsset const a = mptt.issuanceID();
            mptt.authorize({.account = owner});
            mptt.authorize({.account = holder});
            mptt.authorize({.account = borrower});
            env.close();
            env(pay(issuer, owner, a(Number{1, 10})));
            env(pay(issuer, holder, a(Number{1, 10})));
            env(pay(issuer, borrower, a(Number{1, 10})));
            env.close();
            return a;
        }
        PrettyAsset const a = issuer["USD"];
        // Clawback must be enabled while the issuer has no trust line yet.
        env(fset(issuer, asfAllowTrustLineClawback));
        env.close();
        env(trust(owner, a(Number{1, 11})));
        env(trust(holder, a(Number{1, 11})));
        env(trust(borrower, a(Number{1, 11})));
        env.close();
        env(pay(issuer, owner, a(Number{1, 10})));
        env(pay(issuer, holder, a(Number{1, 10})));
        env(pay(issuer, borrower, a(Number{1, 10})));
        env.close();
        return a;
    }();

    jtx::Vault vault{env};
    std::optional<Keylet> vaultKeylet;
    NetClock::time_point subscriptionDate{};
    NetClock::time_point redemptionDate{};
    if (openEnded)
    {
        auto const [tx, keylet] = vault.create({.owner = owner, .asset = asset.raw()});
        env(tx);
        vaultKeylet = keylet;
    }
    else
    {
        // Dates aligned to the close-time resolution, so a ledger can close exactly on them.
        subscriptionDate = alignedTime(env, env.now() + kBrokerSubscriptionOffset);
        redemptionDate = alignedTime(env, subscriptionDate + investmentWindow);
        auto const [tx, keylet] = vault.create(
            {.owner = owner,
             .asset = asset.raw(),
             .vaultKind = std::to_underlying(VaultKind::ClosedEnded),
             .subscriptionDate = timeCount(subscriptionDate),
             .redemptionDate = timeCount(redemptionDate)});
        env(tx);
        vaultKeylet = keylet;
    }
    env.close();
    if (seed != Number{0})
    {
        env(jtx::Vault::deposit(
                {.depositor = holder, .id = vaultKeylet->key, .amount = asset(seed)}),
            jtx::Ter(tesSUCCESS));
        env.close();
    }

    Keylet brokerKeylet{ltLOAN_BROKER, UInt256{}};
    if (config)
    {
        using namespace loan_broker;
        brokerKeylet = keylet::loanBroker(owner.id(), SeqProxy::rawSequence(env.seq(owner)));
        auto tx = set(owner, vaultKeylet->key);
        if (config->debtMaximum)
            tx[sfDebtMaximum] = *config->debtMaximum;
        if (config->managementFeeRate)
            tx[sfManagementFeeRate] = *config->managementFeeRate;
        if (config->coverRateMinimum)
            tx[sfCoverRateMinimum] = *config->coverRateMinimum;
        if (config->coverRateLiquidation)
            tx[sfCoverRateLiquidation] = *config->coverRateLiquidation;
        env(tx, jtx::Ter(tesSUCCESS));
        env.close();
        if (!env.le(brokerKeylet))
            throw std::runtime_error("setUpBrokerVault: the loan broker was not created");
    }

    if (!openEnded && toInvestment)
        vault.closePastSubscription(subscriptionDate);

    return {
        owner,
        issuer,
        holder,
        borrower,
        asset,
        *vaultKeylet,
        brokerKeylet,
        subscriptionDate,
        redemptionDate};
}

// The account's balance of the vault asset (IOU or MPT) as a Number.
[[nodiscard]] inline Number
assetBalance(jtx::Env& env, jtx::Account const& account, jtx::PrettyAsset const& asset)
{
    return Number{env.balance(account, asset.raw()).value()};
}

// The owner deposits `amount` of first-loss cover.
inline void
depositCover(jtx::Env& env, BrokerFixture const& f, Number const& amount)
{
    using namespace jtx;
    env(loan_broker::coverDeposit(f.owner, f.brokerKeylet.key, f.asset(amount)),
        jtx::Ter(tesSUCCESS));
    env.close();
}

// The close time stamped on the open ledger: the start date LoanSet gives a one-step loan.
[[nodiscard]] inline std::uint32_t
ledgerCloseTime(jtx::Env& env)
{
    return env.current()->header().closeTime.time_since_epoch().count();
}

// Close the ledger so that the next transaction's parent close time is at least `at`.
inline void
closeAt(jtx::Env& env, std::uint32_t at)
{
    env.close(NetClock::time_point{NetClock::duration{at}});
}

// Snapshot the loan on `view` (and its broker) into the model's Loan DTO. The payment total is
// not stored on the loan, so the caller supplies the one it submitted.
[[nodiscard]] inline Loan
readLoan(
    ReadView const& view,
    Keylet const& loanKeylet,
    Asset const& asset,
    std::uint32_t paymentTotal)
{
    auto const sle = view.read(loanKeylet);
    if (!sle)
        throw std::runtime_error("readLoan: no loan on the view");
    return Loan{
        .broker = readBroker(view, keylet::loanBroker(sle->at(sfLoanBrokerID)), asset),
        .interestRate = sle->at(sfInterestRate),
        .lateInterestRate = sle->at(sfLateInterestRate),
        .closeInterestRate = sle->at(sfCloseInterestRate),
        .overpaymentInterestRate = sle->at(sfOverpaymentInterestRate),
        .overpaymentFee = sle->at(sfOverpaymentFee),
        .originationFee = sle->at(sfLoanOriginationFee),
        .serviceFee = sle->at(sfLoanServiceFee),
        .latePaymentFee = sle->at(sfLatePaymentFee),
        .closePaymentFee = sle->at(sfClosePaymentFee),
        .paymentInterval = sle->at(sfPaymentInterval),
        .paymentTotal = paymentTotal,
        .gracePeriod = sle->at(sfGracePeriod),
        .startDate = sle->at(sfStartDate),
        .paymentRemaining = sle->at(sfPaymentRemaining),
        .periodicPayment = sle->at(sfPeriodicPayment),
        .principalOutstanding = sle->at(sfPrincipalOutstanding),
        .totalValueOutstanding = sle->at(sfTotalValueOutstanding),
        .managementFeeOutstanding = sle->at(sfManagementFeeOutstanding),
        .loanScale = static_cast<std::int32_t>(sle->at(sfLoanScale)),
        .previousPaymentDueDate = sle->at(sfPreviousPaymentDueDate),
        .nextPaymentDueDate = sle->at(sfNextPaymentDueDate),
        .isPending = sle->isFlag(lsfLoanPending),
        .isImpaired = sle->isFlag(lsfLoanImpaired),
        .isDefault = sle->isFlag(lsfLoanDefault),
        .allowsOverpayment = sle->isFlag(lsfLoanOverpayment)};
}

// The LoanSet fields of a test loan: a 1000 principal in two installments 600 s apart, no interest
// and no fees unless set. A start date makes it a two-step proposal submitted by the owner.
struct LoanParams
{
    Number principal{1'000};
    std::uint32_t interestRate{};
    std::uint32_t lateInterestRate{};
    std::uint32_t closeInterestRate{};
    std::uint32_t overpaymentInterestRate{};
    std::uint32_t overpaymentFee{};
    Number originationFee{0};
    Number serviceFee{0};
    Number latePaymentFee{0};
    Number closePaymentFee{0};
    std::uint32_t paymentInterval = 600;
    std::uint32_t paymentTotal = 2;
    std::optional<std::uint32_t> gracePeriod;
    std::optional<std::uint32_t> startDate;
    bool allowsOverpayment = false;
};

[[nodiscard]] inline LoanSetArgs
loanSetArgs(LoanParams const& p)
{
    return LoanSetArgs{
        .principal = p.principal,
        .interestRate = p.interestRate,
        .lateInterestRate = p.lateInterestRate,
        .closeInterestRate = p.closeInterestRate,
        .overpaymentInterestRate = p.overpaymentInterestRate,
        .overpaymentFee = p.overpaymentFee,
        .originationFee = p.originationFee,
        .serviceFee = p.serviceFee,
        .latePaymentFee = p.latePaymentFee,
        .closePaymentFee = p.closePaymentFee,
        .paymentInterval = p.paymentInterval,
        .paymentTotal = p.paymentTotal,
        .gracePeriod = p.gracePeriod,
        .startDate = p.startDate,
        .allowsOverpayment = p.allowsOverpayment};
}

// The configuration half of the loan LoanSet would create, for reading the model's result back.
[[nodiscard]] inline Loan
loanTemplate(LoanBroker const& broker, LoanParams const& p, std::uint32_t startDate)
{
    return Loan{
        .broker = broker,
        .interestRate = p.interestRate,
        .lateInterestRate = p.lateInterestRate,
        .closeInterestRate = p.closeInterestRate,
        .overpaymentInterestRate = p.overpaymentInterestRate,
        .overpaymentFee = p.overpaymentFee,
        .originationFee = p.originationFee,
        .serviceFee = p.serviceFee,
        .latePaymentFee = p.latePaymentFee,
        .closePaymentFee = p.closePaymentFee,
        .paymentInterval = p.paymentInterval,
        .paymentTotal = p.paymentTotal,
        .gracePeriod = p.gracePeriod.value_or(60),
        .startDate = startDate,
        .allowsOverpayment = p.allowsOverpayment};
}

// The LoanSet transaction for `p`. A one-step loan is submitted by the borrower and must be sent
// with the owner's counterparty signature and a double fee (see submitLoanSet).
[[nodiscard]] inline json::Value
loanSetTx(BrokerFixture const& f, LoanParams const& p)
{
    using namespace jtx;
    bool const twoStep = p.startDate.has_value();
    auto tx = loan::set(
        twoStep ? f.owner : f.borrower,
        f.brokerKeylet.key,
        p.principal,
        p.allowsOverpayment ? std::uint32_t{tfLoanOverpayment} : 0);
    if (twoStep)
    {
        tx[sfBorrower] = f.borrower.human();
        tx[sfStartDate] = *p.startDate;
    }
    if (p.interestRate)
        tx[sfInterestRate] = p.interestRate;
    if (p.lateInterestRate)
        tx[sfLateInterestRate] = p.lateInterestRate;
    if (p.closeInterestRate)
        tx[sfCloseInterestRate] = p.closeInterestRate;
    if (p.overpaymentInterestRate)
        tx[sfOverpaymentInterestRate] = p.overpaymentInterestRate;
    if (p.overpaymentFee)
        tx[sfOverpaymentFee] = p.overpaymentFee;
    if (p.originationFee != Number{0})
        tx[sfLoanOriginationFee] = p.originationFee;
    if (p.serviceFee != Number{0})
        tx[sfLoanServiceFee] = p.serviceFee;
    if (p.latePaymentFee != Number{0})
        tx[sfLatePaymentFee] = p.latePaymentFee;
    if (p.closePaymentFee != Number{0})
        tx[sfClosePaymentFee] = p.closePaymentFee;
    tx[sfPaymentInterval] = p.paymentInterval;
    tx[sfPaymentTotal] = p.paymentTotal;
    if (p.gracePeriod)
        tx[sfGracePeriod] = *p.gracePeriod;
    return tx;
}

// The keylet of the broker's next loan on the view.
[[nodiscard]] inline Keylet
nextLoan(ReadView const& view, BrokerFixture const& f)
{
    return keylet::loan(
        f.brokerKeylet.key, SeqProxy::rawSequence(view.read(f.brokerKeylet)->at(sfLoanSequence)));
}

// Submit the LoanSet for `p`, expecting success, and return the loan's keylet.
inline Keylet
submitLoanSet(jtx::Env& env, BrokerFixture const& f, LoanParams const& p)
{
    using namespace jtx;
    auto const loanKeylet = nextLoan(*env.current(), f);
    auto const tx = loanSetTx(f, p);
    if (p.startDate)
        env(tx, jtx::Ter(tesSUCCESS));
    else
        env(tx,
            Sig(sfCounterpartySignature, f.owner),
            Fee(env.current()->fees().base * 2),
            jtx::Ter(tesSUCCESS));
    env.close();
    if (!env.le(loanKeylet))
        throw std::runtime_error("submitLoanSet: the loan was not created");
    return loanKeylet;
}

// The borrower takes a one-step loan of `principal` with the default schedule.
inline Keylet
issueLoan(jtx::Env& env, BrokerFixture const& f, Number const& principal)
{
    return submitLoanSet(env, f, LoanParams{.principal = principal});
}

// ---- Staging on a throwaway view ------------------------------------------------------------

[[nodiscard]] inline LoanBroker
readBroker(ReadView const& view, BrokerFixture const& f)
{
    return readBroker(view, f.brokerKeylet, f.asset.raw());
}

// Apply `tx` on `view`, with the sender's sequence read from the view (several transactions of
// one account can be applied to the same view).
template <class... Fn>
TER
applyOn(jtx::Env& env, OpenView& view, json::Value tx, Fn const&... fn)
{
    auto const sender = parseBase58<AccountID>(tx[jss::Account].asString());
    auto const account = view.read(keylet::account(*sender));
    auto const jt = env.jt(tx, jtx::Seq(account->at(sfSequence)), fn...);
    return xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
}

// Apply a LoanSet for `p` on the view: one-step (borrower, with the owner's signature) or, with a
// start date, two-step (owner).
inline TER
applyLoanSet(jtx::Env& env, OpenView& view, BrokerFixture const& f, LoanParams const& p)
{
    if (p.startDate)
        return applyOn(env, view, loanSetTx(f, p));
    return applyOn(
        env,
        view,
        loanSetTx(f, p),
        jtx::Sig(sfCounterpartySignature, f.owner),
        jtx::Fee(env.current()->fees().base * 2));
}

// n units of the fixture's grid: one MPT unit, or 1e-6 for the scale-6 IOU vault.
[[nodiscard]] inline Number
units(BrokerFixture const& f, std::int64_t n)
{
    return f.asset.raw().holds<MPTIssue>() ? Number{n} : Number{n, -6};
}

[[nodiscard]] inline std::string
assetName(BrokerFixture const& f)
{
    return f.asset.raw().holds<MPTIssue>() ? "MPT" : "IOU";
}

// What a non-issuer account holds of the fixture asset on `view`.
[[nodiscard]] inline Number
holding(ReadView const& view, jtx::Account const& account, Asset const& asset)
{
    if (asset.holds<MPTIssue>())
    {
        auto const token =
            view.read(keylet::mptoken(asset.get<MPTIssue>().getMptID(), account.id()));
        return token ? Number{static_cast<std::int64_t>(token->getFieldU64(sfMPTAmount))}
                     : Number{};
    }
    Issue const issue = asset.get<Issue>();
    auto const line = view.read(keylet::trustLine(account.id(), issue));
    if (!line)
        return Number{};
    Number const balance = line->getFieldAmount(sfBalance);
    return account.id() > issue.account ? -balance : balance;
}

// The loan LoanSet creates on `view` for `p`; it must succeed.
inline Keylet
createLoan(jtx::Env& env, OpenView& view, BrokerFixture const& f, LoanParams const& p)
{
    Keylet const loan = nextLoan(view, f);
    TER const ter = applyLoanSet(env, view, f, p);
    if (!isTesSuccess(ter))
        throw std::runtime_error("createLoan: LoanSet failed with " + transToken(ter));
    return loan;
}

// Move the loan's dates back by `seconds`, as if that much time had passed for it.
inline void
ageLoan(OpenView& view, Keylet const& loan, std::int64_t seconds)
{
    Sandbox sb(&view, TapNone);
    auto const sle = sb.peek(loan);
    for (SF_UINT32 const* field : {&sfStartDate, &sfPreviousPaymentDueDate, &sfNextPaymentDueDate})
    {
        if (sle->isFieldPresent(*field) && sle->getFieldU32(*field) != 0)
            sle->setFieldU32(
                *field, static_cast<std::uint32_t>(sle->getFieldU32(*field) - seconds));
    }
    sb.update(sle);
    sb.apply(view);
}

// The loan started `age` seconds before the parent close time `now`.
inline void
startedAgo(OpenView& view, Keylet const& loan, std::uint32_t now, std::int64_t age)
{
    ageLoan(view, loan, std::int64_t{view.read(loan)->at(sfStartDate)} - (now - age));
}

// The loan's next payment falls due `offset` seconds after the parent close time `now`.
inline void
dueAt(OpenView& view, Keylet const& loan, std::uint32_t now, std::int64_t offset)
{
    ageLoan(view, loan, std::int64_t{view.read(loan)->at(sfNextPaymentDueDate)} - (now + offset));
}

// Stage the vault's deployed assets and unrealized loss (assets total follows, Downward).
inline void
stageDeployed(OpenView& view, Keylet const& vault, Number const& deployed, Number const& loss)
{
    Sandbox sb(&view, TapNone);
    auto const v = sb.peek(vault);
    v->at(sfAssetsDeployed) = deployed;
    v->at(sfLossUnrealized) = loss;
    {
        NumberRoundModeGuard const rg(Number::RoundingMode::Downward);
        v->at(sfAssetsTotal) = STAmount{Asset{v->at(sfAsset)}, getAssetsTotal(v)};
    }
    sb.update(v);
    sb.apply(view);
}

// State reached before the swept transaction, on the throwaway view.
struct LendingStage
{
    // A zero-interest one-payment loan of this many units, taken first (the broker's debt).
    std::int64_t debt = 0;
    // First-loss cover deposited by the owner (real transaction), in units.
    std::int64_t cover = 0;
    std::uint16_t managementFeeRate = 0;
    // Minimum cover rate; a non-zero rate also gets the fixture's 20% liquidation rate.
    std::uint32_t coverRate = 0;
    std::optional<std::int64_t> debtMaximum;  // in units
    // Vault fields: closed-ended dates (seconds since the epoch) and unrealized yield in units.
    std::optional<std::uint32_t> subscriptionDate;
    std::optional<std::uint32_t> redemptionDate;
    std::int64_t yield = 0;
};

inline std::string
stageText(LendingStage const& s)
{
    std::string t = "debt " + std::to_string(s.debt) + " cover " + std::to_string(s.cover);
    if (s.coverRate)
        t += " rate " + std::to_string(s.coverRate);
    if (s.debtMaximum)
        t += " maximum " + std::to_string(*s.debtMaximum);
    if (s.yield)
        t += " yield " + std::to_string(s.yield);
    if (s.subscriptionDate)
        t += " sub " + std::to_string(*s.subscriptionDate) + " red " +
            std::to_string(*s.redemptionDate);
    return t;
}

// Reach `s` on `view`. Dates, yield, rates and the debt maximum are staged fields; the debt loan
// and the cover deposit are real transactions, applied after the dates and before the rates (so
// the debt loan needs no cover). Throws when a real transaction fails.
inline void
stageLending(jtx::Env& env, OpenView& view, BrokerFixture const& f, LendingStage const& s)
{
    {
        Sandbox sb(&view, TapNone);
        auto vault = sb.peek(f.vaultKeylet);
        if (s.subscriptionDate && s.redemptionDate)
        {
            vault->at(sfSubscriptionDate) = *s.subscriptionDate;
            vault->at(sfRedemptionDate) = *s.redemptionDate;
        }
        if (s.yield)
        {
            vault->at(sfYieldUnrealized) = units(f, s.yield);
            NumberRoundModeGuard const rg(Number::RoundingMode::Downward);
            vault->at(sfAssetsTotal) = STAmount{f.asset.raw(), getAssetsTotal(vault)};
        }
        sb.update(vault);
        sb.apply(view);
    }
    if (s.debt > 0)
    {
        TER const ter = applyLoanSet(
            env, view, f, LoanParams{.principal = units(f, s.debt), .paymentTotal = 1});
        if (ter != tesSUCCESS)
            throw std::runtime_error("stageLending: debt loan " + transToken(ter));
    }
    if (s.cover > 0)
    {
        TER const ter = applyOn(
            env,
            view,
            jtx::loan_broker::coverDeposit(
                f.owner, f.brokerKeylet.key, f.asset(units(f, s.cover))));
        if (ter != tesSUCCESS)
            throw std::runtime_error("stageLending: cover deposit " + transToken(ter));
    }
    Sandbox sb(&view, TapNone);
    auto broker = sb.peek(f.brokerKeylet);
    if (s.managementFeeRate)
        broker->at(sfManagementFeeRate) = s.managementFeeRate;
    if (s.coverRate)
    {
        broker->at(sfCoverRateMinimum) = s.coverRate;
        broker->at(sfCoverRateLiquidation) = 20'000;
    }
    if (s.debtMaximum)
        broker->at(sfDebtMaximum) = units(f, *s.debtMaximum);
    sb.update(broker);
    sb.apply(view);
}

// Investment phase from 1'000 s before the parent close time until far after it.
[[nodiscard]] inline LendingStage
investment(ReadView const& view)
{
    std::uint32_t const pct = view.parentCloseTime().time_since_epoch().count();
    return {.subscriptionDate = pct - 1'000, .redemptionDate = pct + 900'000'000};
}

// The sweep fixture: a broker without cover rates or management fee on a closed-ended vault
// holding `seedUnits`. The clock then moves 1e8 s on, so staged dates never wrap; the vault's own
// dates are past, so every check stages its phase dates.
inline BrokerFixture
setUpSweepBroker(jtx::Env& env, LendingAsset kind, std::int64_t seedUnits)
{
    BrokerConfig const config{
        .managementFeeRate = std::nullopt,
        .coverRateMinimum = std::nullopt,
        .coverRateLiquidation = std::nullopt};
    Number const seed = kind == LendingAsset::iou ? Number{seedUnits, -6} : Number{seedUnits};
    BrokerFixture f = setUpBrokerVault(env, config, seed, false, true, kind);
    env.close(env.now() + std::chrono::seconds{100'000'000});
    return f;
}

// The model's verdict on a transaction: its preclaim TER, or its doApply TER when preclaim
// accepted (the doApply functions assume preclaim passed).
[[nodiscard]] inline TER
modelVerdict(LawfulTerResult const& can, std::optional<TER> const& applyError)
{
    return can.ter != tesSUCCESS ? can.ter : applyError.value_or(tesSUCCESS);
}

inline void
expectNumber(
    beast::unit_test::Suite& suite,
    char const* name,
    Number const& lean,
    Number const& cpp)
{
    suite.expect(
        lean == cpp, std::string(name) + " lean=" + to_string(lean) + " cpp=" + to_string(cpp));
}

inline void
expectVaultMatches(beast::unit_test::Suite& suite, Vault const& lean, Vault const& cpp)
{
    expectNumber(suite, "vault assetsTotal", lean.assetsTotal, cpp.assetsTotal);
    expectNumber(suite, "vault assetsAvailable", lean.assetsAvailable, cpp.assetsAvailable);
    expectNumber(suite, "vault assetsDeployed", lean.assetsDeployed, cpp.assetsDeployed);
    expectNumber(suite, "vault assetsReserved", lean.assetsReserved, cpp.assetsReserved);
    expectNumber(suite, "vault sharesTotal", lean.sharesTotal, cpp.sharesTotal);
    expectNumber(suite, "vault lossUnrealized", lean.lossUnrealized, cpp.lossUnrealized);
    expectNumber(suite, "vault yieldUnrealized", lean.yieldUnrealized, cpp.yieldUnrealized);
}

inline void
expectBrokerMatches(beast::unit_test::Suite& suite, LoanBroker const& lean, LoanBroker const& cpp)
{
    expectNumber(suite, "broker debtTotal", lean.debtTotal, cpp.debtTotal);
    expectNumber(suite, "broker debtMaximum", lean.debtMaximum, cpp.debtMaximum);
    expectNumber(suite, "broker coverAvailable", lean.coverAvailable, cpp.coverAvailable);
    suite.expect(
        lean.loanCount == cpp.loanCount,
        "broker loanCount lean=" + std::to_string(lean.loanCount) +
            " cpp=" + std::to_string(cpp.loanCount));
}

inline void
expectLoanMatches(beast::unit_test::Suite& suite, Loan const& lean, Loan const& cpp)
{
    suite.expect(
        lean.paymentRemaining == cpp.paymentRemaining,
        "loan paymentRemaining lean=" + std::to_string(lean.paymentRemaining) +
            " cpp=" + std::to_string(cpp.paymentRemaining));
    expectNumber(suite, "loan periodicPayment", lean.periodicPayment, cpp.periodicPayment);
    expectNumber(
        suite, "loan principalOutstanding", lean.principalOutstanding, cpp.principalOutstanding);
    expectNumber(
        suite, "loan totalValueOutstanding", lean.totalValueOutstanding, cpp.totalValueOutstanding);
    expectNumber(
        suite,
        "loan managementFeeOutstanding",
        lean.managementFeeOutstanding,
        cpp.managementFeeOutstanding);
    suite.expect(
        lean.loanScale == cpp.loanScale,
        "loan scale lean=" + std::to_string(lean.loanScale) +
            " cpp=" + std::to_string(cpp.loanScale));
    suite.expect(
        lean.previousPaymentDueDate == cpp.previousPaymentDueDate &&
            lean.nextPaymentDueDate == cpp.nextPaymentDueDate,
        "loan due dates lean=" + std::to_string(lean.previousPaymentDueDate) + "/" +
            std::to_string(lean.nextPaymentDueDate) +
            " cpp=" + std::to_string(cpp.previousPaymentDueDate) + "/" +
            std::to_string(cpp.nextPaymentDueDate));
    suite.expect(
        lean.isPending == cpp.isPending && lean.isImpaired == cpp.isImpaired &&
            lean.isDefault == cpp.isDefault && lean.allowsOverpayment == cpp.allowsOverpayment,
        "loan flags differ");
    // The configuration the model was given must be what the ledger stored.
    suite.expect(
        lean.interestRate == cpp.interestRate && lean.lateInterestRate == cpp.lateInterestRate &&
            lean.closeInterestRate == cpp.closeInterestRate &&
            lean.overpaymentInterestRate == cpp.overpaymentInterestRate &&
            lean.overpaymentFee == cpp.overpaymentFee,
        "loan rates differ");
    expectNumber(suite, "loan originationFee", lean.originationFee, cpp.originationFee);
    expectNumber(suite, "loan serviceFee", lean.serviceFee, cpp.serviceFee);
    expectNumber(suite, "loan latePaymentFee", lean.latePaymentFee, cpp.latePaymentFee);
    expectNumber(suite, "loan closePaymentFee", lean.closePaymentFee, cpp.closePaymentFee);
    suite.expect(
        lean.paymentInterval == cpp.paymentInterval && lean.gracePeriod == cpp.gracePeriod &&
            lean.startDate == cpp.startDate,
        "loan schedule lean=" + std::to_string(lean.paymentInterval) + "/" +
            std::to_string(lean.gracePeriod) + "/" + std::to_string(lean.startDate) +
            " cpp=" + std::to_string(cpp.paymentInterval) + "/" + std::to_string(cpp.gracePeriod) +
            "/" + std::to_string(cpp.startDate));
}

}  // namespace xrpl::test::formal_verification
