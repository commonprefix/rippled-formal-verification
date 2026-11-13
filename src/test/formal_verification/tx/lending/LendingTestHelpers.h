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
#include <exception>
#include <initializer_list>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace xrpl::test::formal_verification {

// The amendments every lending suite enables; the expected verdicts are for this set.
[[nodiscard]] inline FeatureBitset
lendingTestAmendments()
{
    return jtx::testableAmendments();
}

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

enum class LendingAsset : std::uint8_t { iou, mpt };

// A closed-ended vault owned by `owner` with its loan broker. The holder is the vault's lender,
// the owner funds the broker cover, the borrower takes loans.
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
    std::optional<Number> debtMaximum{};
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
            // The owner holds 1e16 units, as on the IOU vault, so cover reaches the open limit.
            env(pay(issuer, owner, a(Number{1, 16})));
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
    std::optional<std::uint32_t> gracePeriod{};
    std::optional<std::uint32_t> startDate{};
    bool allowsOverpayment = false;
};

// The loan's fields as they appear in failure messages.
[[nodiscard]] inline std::string
loanText(LoanParams const& p)
{
    std::string t = " principal " + to_string(p.principal) + " count " +
        std::to_string(p.paymentTotal) + " interval " + std::to_string(p.paymentInterval);
    for (auto const& [name, rate] : {
             std::pair{" rate ", p.interestRate},
             std::pair{" late rate ", p.lateInterestRate},
             std::pair{" close rate ", p.closeInterestRate},
         })
    {
        if (rate != 0u)
            t += name + std::to_string(rate);
    }
    for (auto const& [name, fee] : {
             std::pair{" origination fee ", p.originationFee},
             std::pair{" service fee ", p.serviceFee},
             std::pair{" late fee ", p.latePaymentFee},
             std::pair{" close fee ", p.closePaymentFee},
         })
    {
        if (fee != Number{0})
            t += name + to_string(fee);
    }
    if (p.gracePeriod)
        t += " grace " + std::to_string(*p.gracePeriod);
    if (p.startDate)
        t += " start " + std::to_string(*p.startDate);
    return t;
}

// Snapshot the loan on `view` (and its broker) into the model's Loan DTO. The payment total and the
// requested principal are not stored on the loan, so they come from the submitted `p`.
[[nodiscard]] inline Loan
readLoan(
    ReadView const& view,
    Keylet const& loanKeylet,
    BrokerFixture const& f,
    LoanParams const& p)
{
    auto const sle = view.read(loanKeylet);
    if (!sle)
        throw std::runtime_error("readLoan: no loan on the view");
    return Loan{
        .broker = readBroker(view, keylet::loanBroker(sle->at(sfLoanBrokerID)), f.asset.raw()),
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
        .paymentTotal = p.paymentTotal,
        .gracePeriod = sle->at(sfGracePeriod),
        .startDate = sle->at(sfStartDate),
        .paymentRemaining = sle->at(sfPaymentRemaining),
        .principalInitial = p.principal,
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
        .principalInitial = p.principal,
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

// Staging writes ledger entries directly on a throwaway view (loan dates moved back, vault and
// broker fields set) and applies the transaction there with unlimited flags. It reaches states no
// transaction sequence may: a loan due at an arbitrary instant, deployed assets or an unrealized
// loss unrelated to the loans, a broker rate changed under existing loans. A test compares the
// model and C++ on the same pre-state; its verdict is not a claim that the state is reachable.

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
    if (!sender)
        throw std::runtime_error("applyOn: no Account on the transaction");
    auto const account = view.read(keylet::account(*sender));
    if (!account)
        throw std::runtime_error("applyOn: no sender account on the view");
    auto const jt = env.jt(tx, jtx::Seq(account->at(sfSequence)), fn...);
    return xrpl::apply(env.app(), view, *jt.stx, TapUnlimited, env.journal).ter;
}

// n * 10^exponent units of the fixture's grid: one MPT unit, or 1e-6 for the scale-6 IOU vault.
[[nodiscard]] inline Number
units(BrokerFixture const& f, std::int64_t n, int exponent = 0)
{
    return f.asset.raw().holds<MPTIssue>() ? Number{n, exponent} : Number{n, exponent - 6};
}

// `n` (in asset units) as grid units of the fixture's vault.
[[nodiscard]] inline std::int64_t
toUnits(ReadView const& view, BrokerFixture const& f, Number const& n)
{
    return static_cast<std::int64_t>(
        n * Number{1, static_cast<int>(view.read(f.vaultKeylet)->at(sfScale))});
}

[[nodiscard]] inline std::string
assetName(BrokerFixture const& f)
{
    return f.asset.raw().holds<MPTIssue>() ? "MPT" : "IOU";
}

// A shared ledger (one per asset) that the staged single-value tests and the case lists run on.
struct TestLedger
{
    jtx::Env* env;
    BrokerFixture f;
};

// What a non-issuer account holds of the fixture asset on `view`.
[[nodiscard]] inline Number
holding(ReadView const& view, AccountID const& account, Asset const& asset)
{
    if (asset.holds<MPTIssue>())
    {
        auto const token = view.read(keylet::mptoken(asset.get<MPTIssue>().getMptID(), account));
        return token ? Number{static_cast<std::int64_t>(token->getFieldU64(sfMPTAmount))}
                     : Number{};
    }
    Issue const issue = asset.get<Issue>();
    auto const line = view.read(keylet::trustLine(account, issue));
    if (!line)
        return Number{};
    Number const balance = line->getFieldAmount(sfBalance);
    return account > issue.account ? -balance : balance;
}

[[nodiscard]] inline Number
holding(ReadView const& view, jtx::Account const& account, Asset const& asset)
{
    return holding(view, account.id(), asset);
}

// A loan transaction C++ applied on a staged view: the model's inputs (the loan before, with its
// broker, the pool and both clocks), the verdict, the loan (with its broker) and pool after, and
// what the transaction moved, when the caller measured it.
struct AppliedLoanTx
{
    Loan pre{};
    Vault pool{};
    std::uint32_t parentCloseTime{};
    std::uint32_t closeTime{};
    TER ter{};
    Loan post{};
    Vault poolAfter{};
    std::optional<Number> toBorrower{};
    std::optional<Number> toPool{};
    std::optional<Number> toBroker{};
    // What left the broker's pseudo-account.
    std::optional<Number> fromBroker{};
    bool erased{};
};

// The model's answer: preclaim (`can`), then doApply's result.
struct LeanLoanTx
{
    LawfulTerResult can{};
    LeanLoanResult result{};
};

// The model's answer to a LoanDelete: preclaim (`can`), then doApply's broker and pool.
struct LeanDeleteTx
{
    LawfulTerResult can{};
    LeanBrokerPoolResult result{};
};

// The pre-state of a loan transaction on `view`: `pre`, the pool and the clocks.
[[nodiscard]] inline AppliedLoanTx
loanTxBefore(ReadView const& view, BrokerFixture const& f, Loan const& pre)
{
    return {
        .pre = pre,
        .pool = readVaultState(view, f.vaultKeylet, f.asset.raw()),
        .parentCloseTime =
            static_cast<std::uint32_t>(view.parentCloseTime().time_since_epoch().count()),
        .closeTime = static_cast<std::uint32_t>(view.header().closeTime.time_since_epoch().count()),
    };
}

// LoanSet for `p` on `view`: one-step (borrower, with the owner's signature) or, with a start
// date, two-step (owner). The pre-state is the loan it would create (see loanTemplate). The amount
// to the borrower is exact only when the borrower holds no IOU (see zeroIouBalance).
[[nodiscard]] inline AppliedLoanTx
applyLoanSet(jtx::Env& env, OpenView& view, BrokerFixture const& f, LoanParams const& p)
{
    std::uint32_t const closeTime = view.header().closeTime.time_since_epoch().count();
    Keylet const loan = nextLoan(view, f);
    AppliedLoanTx a = loanTxBefore(
        view, f, loanTemplate(readBroker(view, f), p, p.startDate.value_or(closeTime)));
    Number const before = holding(view, f.borrower, f.asset.raw());
    Number const ownerBefore = holding(view, f.owner, f.asset.raw());
    a.ter = p.startDate ? applyOn(env, view, loanSetTx(f, p))
                        : applyOn(
                              env,
                              view,
                              loanSetTx(f, p),
                              jtx::Sig(sfCounterpartySignature, f.owner),
                              jtx::Fee(env.current()->fees().base * 2));
    a.post = a.ter == tesSUCCESS ? readLoan(view, loan, f, p) : a.pre;
    a.poolAfter = readVaultState(view, f.vaultKeylet, f.asset.raw());
    a.toBorrower = holding(view, f.borrower, f.asset.raw()) - before;
    a.toBroker = holding(view, f.owner, f.asset.raw()) - ownerBefore;
    return a;
}

// The model of LoanSet on the pre-state C++ saw. Both canCreate (preclaim) and create (doApply)
// run, as a model error of create stands for a C++ preflight rejection.
[[nodiscard]] inline LeanLoanTx
leanLoanSet(AppliedLoanTx const& cpp, LoanParams const& p)
{
    LoanSetArgs const args = loanSetArgs(p);
    return {
        .can =
            leanCanLoanCreate(cpp.pre.broker, cpp.pool, args, cpp.closeTime, cpp.parentCloseTime),
        .result = leanLoanCreate(cpp.pre.broker, cpp.pool, args, cpp.closeTime, cpp.pre),
    };
}

// LoanAccept by the borrower of the proposal at `loan` (submitted with `p`) on `view`. The amount
// to the borrower is exact only when the borrower holds no IOU.
[[nodiscard]] inline AppliedLoanTx
applyLoanAccept(
    jtx::Env& env,
    OpenView& view,
    BrokerFixture const& f,
    Keylet const& loan,
    LoanParams const& p)
{
    AppliedLoanTx a = loanTxBefore(view, f, readLoan(view, loan, f, p));
    Number const before = holding(view, f.borrower, f.asset.raw());
    Number const ownerBefore = holding(view, f.owner, f.asset.raw());
    a.ter = applyOn(env, view, jtx::loan::accept(f.borrower, loan.key));
    a.post = readLoan(view, loan, f, p);
    a.poolAfter = readVaultState(view, f.vaultKeylet, f.asset.raw());
    a.toBorrower = holding(view, f.borrower, f.asset.raw()) - before;
    a.toBroker = holding(view, f.owner, f.asset.raw()) - ownerBefore;
    return a;
}

// The model of LoanAccept on the pre-state C++ saw: accept only runs when canAccept passes.
[[nodiscard]] inline LeanLoanTx
leanLoanAccept(AppliedLoanTx const& cpp)
{
    LeanLoanTx lean{.can = leanCanLoanAccept(cpp.pre, cpp.pool, cpp.parentCloseTime)};
    if (!lean.can.leanError && lean.can.ter == tesSUCCESS)
        lean.result = leanLoanAccept(cpp.pre, cpp.pool);
    return lean;
}

[[nodiscard]] inline std::uint32_t
payFlags(PaymentType type)
{
    switch (type)
    {
        case PaymentType::regular:
            return 0;
        case PaymentType::late:
            return tfLoanLatePayment;
        case PaymentType::full:
            return tfLoanFullPayment;
        case PaymentType::overpayment:
            return tfLoanOverpayment;
    }
    return 0;
}

// LoanPay of `amount` by the borrower on the loan at `loan` (submitted with `p`) on `view`. What
// the pool gained and what the broker got (its cover plus the owner's holding) are measured; the
// owner's change is exact only when it holds no IOU (see zeroIouBalance).
[[nodiscard]] inline AppliedLoanTx
applyLoanPay(
    jtx::Env& env,
    OpenView& view,
    BrokerFixture const& f,
    Keylet const& loan,
    LoanParams const& p,
    PaymentType type,
    Number const& amount)
{
    AppliedLoanTx a = loanTxBefore(view, f, readLoan(view, loan, f, p));
    Number const ownerBefore = holding(view, f.owner, f.asset.raw());
    // LoanPay's fee grows with the instalments one transaction may settle (up to 100).
    a.ter = applyOn(
        env,
        view,
        jtx::loan::pay(f.borrower, loan.key, f.asset(amount), payFlags(type)),
        jtx::Fee(env.current()->fees().base * 101));
    a.post = readLoan(view, loan, f, p);
    a.poolAfter = readVaultState(view, f.vaultKeylet, f.asset.raw());
    a.toPool = a.poolAfter.assetsAvailable - a.pool.assetsAvailable;
    a.toBroker = (a.post.broker.coverAvailable - a.pre.broker.coverAvailable) +
        (holding(view, f.owner, f.asset.raw()) - ownerBefore);
    return a;
}

// The model of LoanPay on the pre-state C++ saw: pay only runs when canPay passes.
[[nodiscard]] inline LeanLoanTx
leanLoanPay(AppliedLoanTx const& cpp, PaymentType type, Number const& amount)
{
    LeanLoanTx lean{.can = leanCanLoanPay(cpp.pre, type)};
    if (!lean.can.leanError && lean.can.ter == tesSUCCESS)
        lean.result = leanLoanPay(cpp.pre, cpp.pool, type, amount, cpp.parentCloseTime);
    return lean;
}

[[nodiscard]] inline std::uint32_t
manageFlags(ManageAction action)
{
    switch (action)
    {
        case ManageAction::impair:
            return tfLoanImpair;
        case ManageAction::unimpair:
            return tfLoanUnimpair;
        case ManageAction::defaultLoan:
            return tfLoanDefault;
    }
    return 0;
}

// LoanManage `action` by the owner on the loan at `loan` (submitted with `p`) on `view`. What the
// pool gained and what left the broker's pseudo-account (a default moves the cover it consumes
// into the vault) are measured.
[[nodiscard]] inline AppliedLoanTx
applyLoanManage(
    jtx::Env& env,
    OpenView& view,
    BrokerFixture const& f,
    Keylet const& loan,
    LoanParams const& p,
    ManageAction action)
{
    AccountID const pseudo = view.read(f.brokerKeylet)->at(sfAccount);
    Number const heldBefore = holding(view, pseudo, f.asset.raw());
    AppliedLoanTx a = loanTxBefore(view, f, readLoan(view, loan, f, p));
    a.ter = applyOn(env, view, jtx::loan::manage(f.owner, loan.key, manageFlags(action)));
    a.post = readLoan(view, loan, f, p);
    a.poolAfter = readVaultState(view, f.vaultKeylet, f.asset.raw());
    a.toPool = a.poolAfter.assetsAvailable - a.pool.assetsAvailable;
    a.fromBroker = heldBefore - holding(view, pseudo, f.asset.raw());
    return a;
}

// The model of LoanManage on the pre-state C++ saw: manage only runs when canManage passes.
[[nodiscard]] inline LeanLoanTx
leanLoanManage(AppliedLoanTx const& cpp, ManageAction action)
{
    LeanLoanTx lean{.can = leanCanLoanManage(cpp.pre, action, cpp.parentCloseTime)};
    if (!lean.can.leanError && lean.can.ter == tesSUCCESS)
        lean.result = leanLoanManage(cpp.pre, cpp.pool, action, cpp.parentCloseTime);
    return lean;
}

// LoanDelete by `by` of the loan at `loan` (submitted with `p`) on `view`. `post` is the loan
// after, or the loan before when it is gone, with the broker after.
[[nodiscard]] inline AppliedLoanTx
applyLoanDelete(
    jtx::Env& env,
    OpenView& view,
    BrokerFixture const& f,
    Keylet const& loan,
    LoanParams const& p,
    jtx::Account const& by)
{
    AppliedLoanTx a = loanTxBefore(view, f, readLoan(view, loan, f, p));
    a.ter = applyOn(env, view, jtx::loan::del(by, loan.key));
    a.erased = !view.exists(loan);
    a.post = a.erased ? a.pre : readLoan(view, loan, f, p);
    a.post.broker = readBroker(view, f);
    a.poolAfter = readVaultState(view, f.vaultKeylet, f.asset.raw());
    return a;
}

// The model of LoanDelete on the pre-state C++ saw: delete only runs when canDelete passes.
[[nodiscard]] inline LeanDeleteTx
leanLoanDelete(AppliedLoanTx const& cpp)
{
    LeanDeleteTx lean{.can = leanCanLoanDelete(cpp.pre)};
    if (!lean.can.leanError && lean.can.ter == tesSUCCESS)
        lean.result = leanLoanDelete(cpp.pre, cpp.pool);
    return lean;
}

// Zero `account`'s IOU balance on `view`, so the next change to it is exact (a 16-digit balance
// rounds a small change away). MPT balances are exact integers and stay.
inline void
zeroIouBalance(OpenView& view, jtx::Account const& account, Asset const& asset)
{
    if (!asset.holds<Issue>())
        return;
    Sandbox sb(&view, TapNone);
    auto const line = sb.peek(keylet::trustLine(account.id(), asset.get<Issue>()));
    if (!line)
        return;
    line->setFieldAmount(sfBalance, line->getFieldAmount(sfBalance).zeroed());
    sb.update(line);
    sb.apply(view);
}

// The loan LoanSet creates on `view` for `p`; it must succeed.
inline Keylet
createLoan(jtx::Env& env, OpenView& view, BrokerFixture const& f, LoanParams const& p)
{
    Keylet const loan = nextLoan(view, f);
    TER const ter = applyLoanSet(env, view, f, p).ter;
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
        {
            sle->setFieldU32(
                *field, static_cast<std::uint32_t>(sle->getFieldU32(*field) - seconds));
        }
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

// Stage the vault's available assets at `n` units, held by its pseudo-account (assets total
// follows, Downward).
inline void
stageAvailable(OpenView& view, BrokerFixture const& f, std::int64_t n)
{
    Sandbox sb(&view, TapNone);
    auto const v = sb.peek(f.vaultKeylet);
    Asset const asset = f.asset.raw();
    AccountID const pseudo = v->at(sfAccount);
    v->at(sfAssetsAvailable) = units(f, n);
    {
        NumberRoundModeGuard const rg(Number::RoundingMode::Downward);
        v->at(sfAssetsTotal) = STAmount{asset, getAssetsTotal(v)};
    }
    if (asset.holds<MPTIssue>())
    {
        auto const token = sb.peek(keylet::mptoken(asset.get<MPTIssue>().getMptID(), pseudo));
        token->setFieldU64(sfMPTAmount, static_cast<std::uint64_t>(n));
        sb.update(token);
    }
    else
    {
        stageTrustLine(sb, pseudo, asset.get<Issue>(), units(f, n));
    }
    sb.update(v);
    sb.apply(view);
}

// State reached before the tested transaction, on the throwaway view.
struct LendingStage
{
    // A zero-interest one-payment loan of this many units, taken first (the broker's debt).
    std::int64_t debt = 0;
    // First-loss cover deposited by the owner (real transaction), in units.
    std::int64_t cover = 0;
    std::uint16_t managementFeeRate = 0;
    // Minimum cover rate; a non-zero rate also gets the fixture's 20% liquidation rate.
    std::uint32_t coverRate = 0;
    std::optional<std::int64_t> debtMaximum{};  // in units
    // Vault fields: closed-ended dates (seconds since the epoch) and unrealized yield in units.
    std::optional<std::uint32_t> subscriptionDate{};
    std::optional<std::uint32_t> redemptionDate{};
    std::int64_t yield = 0;
};

inline std::string
stageText(LendingStage const& s)
{
    std::string t = "debt " + std::to_string(s.debt) + " cover " + std::to_string(s.cover);
    if (s.coverRate != 0u)
        t += " rate " + std::to_string(s.coverRate);
    if (s.debtMaximum)
        t += " maximum " + std::to_string(*s.debtMaximum);
    if (s.yield != 0)
        t += " yield " + std::to_string(s.yield);
    if (s.subscriptionDate && s.redemptionDate)
    {
        t += " sub " + std::to_string(*s.subscriptionDate) + " red " +
            std::to_string(*s.redemptionDate);
    }
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
        auto const vault = sb.peek(f.vaultKeylet);
        if (s.subscriptionDate && s.redemptionDate)
        {
            vault->at(sfSubscriptionDate) = *s.subscriptionDate;
            vault->at(sfRedemptionDate) = *s.redemptionDate;
        }
        if (s.yield != 0)
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
        TER const ter =
            applyLoanSet(env, view, f, LoanParams{.principal = units(f, s.debt), .paymentTotal = 1})
                .ter;
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
    auto const broker = sb.peek(f.brokerKeylet);
    if (s.managementFeeRate != 0u)
        broker->at(sfManagementFeeRate) = s.managementFeeRate;
    if (s.coverRate != 0u)
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
    std::uint32_t const parentClose = view.parentCloseTime().time_since_epoch().count();
    return {.subscriptionDate = parentClose - 1'000, .redemptionDate = parentClose + 900'000'000};
}

// The case lists' fixture: a broker without cover rates or management fee on a closed-ended vault
// holding `seedUnits`. The clock then moves 1e8 s on, so staged dates never wrap; the vault's own
// dates are past, so every check stages its phase dates.
inline BrokerFixture
setUpLendingBroker(jtx::Env& env, LendingAsset kind, std::int64_t seedUnits)
{
    BrokerConfig const config{
        .managementFeeRate = std::nullopt,
        .coverRateMinimum = std::nullopt,
        .coverRateLiquidation = std::nullopt,
    };
    Number const seed = kind == LendingAsset::iou ? Number{seedUnits, -6} : Number{seedUnits};
    BrokerFixture f = setUpBrokerVault(env, config, seed, false, true, kind);
    env.close(env.now() + std::chrono::seconds{100'000'000});
    return f;
}

// Run `stage` (staging on a throwaway view); a throw fails the case at `at`. Returns whether it
// staged.
template <class Stage>
bool
tryStage(beast::unit_test::Suite& suite, std::string const& at, Stage&& stage)
{
    try
    {
        stage();
        return true;
    }
    catch (std::exception const& e)
    {
        suite.fail(at + ": " + e.what());
        return false;
    }
}

enum class LoanKind : std::uint8_t { active, pending, defaulted, paidOff };

// A loan with `p` on `view`, started `delay` seconds before the parent close time `now`: a
// proposal starting 1'000 s after `now` when pending, a one-payment loan paid off when paidOff.
// `p` is updated to the submitted fields. A defaulted loan is left to the caller.
inline Keylet
stageLoan(
    jtx::Env& env,
    OpenView& view,
    BrokerFixture const& f,
    LoanParams& p,
    LoanKind kind,
    std::uint32_t now,
    std::int64_t delay)
{
    if (kind == LoanKind::pending)
        p.startDate = now + 1'000;
    if (kind == LoanKind::paidOff)
        p.paymentTotal = 1;
    Keylet const loan = createLoan(env, view, f, p);
    if (kind != LoanKind::pending)
        startedAgo(view, loan, now, delay);
    if (kind == LoanKind::paidOff)
    {
        TER const ter = applyOn(
            env,
            view,
            jtx::loan::pay(f.borrower, loan.key, f.asset(p.principal)),
            jtx::Fee(env.current()->fees().base * 101));
        if (ter != tesSUCCESS)
            throw std::runtime_error("stageLoan: paying off failed with " + transToken(ter));
    }
    return loan;
}

[[nodiscard]] inline std::string
paymentTypeName(PaymentType type)
{
    switch (type)
    {
        case PaymentType::regular:
            return "regular";
        case PaymentType::late:
            return "late";
        case PaymentType::full:
            return "full";
        case PaymentType::overpayment:
            return "overpayment";
    }
    return "?";
}

// ---- Explicit case lists ----------------------------------------------------------------------

// The shared ledgers of the boundary tests: one broker per asset on a vault holding 1e10 units.
struct LendingSetup
{
    TestLedger iouLedger;
    TestLedger mptLedger;
    std::vector<TestLedger> iou;
    std::vector<TestLedger> mpt;
    std::vector<TestLedger> all;
};

inline LendingSetup
setUpLending(jtx::Env& iouEnv, jtx::Env& mptEnv)
{
    TestLedger const iou{
        .env = &iouEnv,
        .f = setUpLendingBroker(iouEnv, LendingAsset::iou, 10'000'000'000),
    };
    TestLedger const mpt{
        .env = &mptEnv,
        .f = setUpLendingBroker(mptEnv, LendingAsset::mpt, 10'000'000'000),
    };
    return {.iouLedger = iou, .mptLedger = mpt, .iou = {iou}, .mpt = {mpt}, .all = {iou, mpt}};
}

// Stage `s` on `view` with the vault in its investment phase (see investment).
inline void
stageInvestment(jtx::Env& env, OpenView& view, BrokerFixture const& f, LendingStage s)
{
    LendingStage const phase = investment(view);
    s.subscriptionDate = phase.subscriptionDate;
    s.redemptionDate = phase.redemptionDate;
    stageLending(env, view, f, s);
}

// A broker transaction C++ applied on a staged view: the model's inputs (the broker and its pool
// before), the verdict, the broker and pool after, and the cover it moved: the broker
// pseudo-account's token change and the change of coverAvailable, both as positive amounts.
struct AppliedBrokerTx
{
    LoanBroker pre{};
    Vault pool{};
    TER ter{};
    LoanBroker post{};
    Vault poolAfter{};
    std::optional<Number> moved{};
    std::optional<Number> booked{};
};

// The model's answer: preclaim (`can`), then doApply's error or broker and the cover it moved.
struct LeanBrokerTx
{
    LawfulTerResult can{};
    std::optional<LeanError> leanError{};
    std::optional<TER> error{};
    LoanBroker broker{};
    std::optional<Number> amount{};
};

// LoanBrokerSet of `args` on `view`: a new broker of the fixture's vault (its pre-state is an
// empty broker of the asset) or, with `update`, an update of the fixture's broker.
[[nodiscard]] inline AppliedBrokerTx
applyLoanBrokerSet(
    jtx::Env& env,
    OpenView& view,
    BrokerFixture const& f,
    LoanBrokerSetArgs const& args,
    bool update)
{
    Asset const asset = f.asset.raw();
    Keylet const broker = update
        ? f.brokerKeylet
        : keylet::loanBroker(
              f.owner.id(),
              SeqProxy::rawSequence(view.read(keylet::account(f.owner.id()))->at(sfSequence)));
    AppliedBrokerTx a{
        .pre =
            update ? readBroker(view, f) : LoanBroker{.numericType = NumericTypeFFI::tagOf(asset)},
        .pool = readVaultState(view, f.vaultKeylet, asset),
    };
    auto tx = jtx::loan_broker::set(f.owner, f.vaultKeylet.key);
    if (update)
        tx[sfLoanBrokerID] = to_string(f.brokerKeylet.key);
    if (args.debtMaximum)
        tx[sfDebtMaximum] = *args.debtMaximum;
    if (args.managementFeeRate)
        tx[sfManagementFeeRate] = *args.managementFeeRate;
    if (args.coverRateMinimum)
        tx[sfCoverRateMinimum] = *args.coverRateMinimum;
    if (args.coverRateLiquidation)
        tx[sfCoverRateLiquidation] = *args.coverRateLiquidation;
    a.ter = applyOn(env, view, tx);
    a.post = a.ter == tesSUCCESS ? readBroker(view, broker, asset) : a.pre;
    a.poolAfter = readVaultState(view, f.vaultKeylet, asset);
    return a;
}

// The model of LoanBrokerSet on the pre-state C++ saw: canCreate / canUpdate is preclaim, create /
// update doApply. Both run, as a model error of doApply stands for a C++ preflight rejection.
[[nodiscard]] inline LeanBrokerTx
leanLoanBrokerSet(AppliedBrokerTx const& cpp, LoanBrokerSetArgs const& args, bool update)
{
    std::uint8_t const nt = cpp.pre.numericType;
    LeanBrokerResult const r =
        update ? leanLoanBrokerUpdate(cpp.pre, args.debtMaximum) : leanLoanBrokerCreate(args, nt);
    return {
        .can = update ? leanCanLoanBrokerUpdate(cpp.pre, cpp.pool, args.debtMaximum)
                      : leanCanLoanBrokerCreate(cpp.pool, args.debtMaximum, nt),
        .leanError = r.leanError,
        .broker = r.broker,
    };
}

enum class CoverOp : std::uint8_t { Deposit, Withdraw, Clawback };

// The amount a cover deposit or withdrawal must carry.
[[nodiscard]] inline STAmount const&
coverAmount(std::optional<STAmount> const& amount)
{
    if (!amount)
        throw std::runtime_error("coverAmount: a cover deposit or withdrawal needs an amount");
    return *amount;
}

// A cover deposit or withdrawal by the owner, or a clawback by the issuer, of `amount` on `view`
// (a clawback without an amount claws everything above the minimum cover).
[[nodiscard]] inline AppliedBrokerTx
applyLoanBrokerCover(
    jtx::Env& env,
    OpenView& view,
    BrokerFixture const& f,
    CoverOp op,
    std::optional<STAmount> const& amount)
{
    using namespace jtx;
    Asset const asset = f.asset.raw();
    AccountID const pseudo = view.read(f.brokerKeylet)->at(sfAccount);
    Number const heldBefore = holding(view, pseudo, asset);
    AppliedBrokerTx a{
        .pre = readBroker(view, f),
        .pool = readVaultState(view, f.vaultKeylet, asset),
    };
    json::Value tx;
    switch (op)
    {
        case CoverOp::Deposit:
            tx = loan_broker::coverDeposit(f.owner, f.brokerKeylet.key, coverAmount(amount));
            break;
        case CoverOp::Withdraw:
            tx = loan_broker::coverWithdraw(f.owner, f.brokerKeylet.key, coverAmount(amount));
            break;
        case CoverOp::Clawback:
            tx = loan_broker::coverClawback(f.issuer);
            tx[sfLoanBrokerID] = to_string(f.brokerKeylet.key);
            if (amount)
                tx[sfAmount] = amount->getJson(JsonOptions::Values::None);
            break;
    }
    a.ter = applyOn(env, view, tx);
    a.post = readBroker(view, f);
    a.poolAfter = readVaultState(view, f.vaultKeylet, asset);
    Number const heldAfter = holding(view, pseudo, asset);
    bool const in = op == CoverOp::Deposit;
    a.moved = in ? heldAfter - heldBefore : heldBefore - heldAfter;
    a.booked = in ? a.post.coverAvailable - a.pre.coverAvailable
                  : a.pre.coverAvailable - a.post.coverAvailable;
    return a;
}

// The model of a cover transaction on the pre-state C++ saw: doApply only runs when preclaim
// accepts (it assumes preclaim passed).
[[nodiscard]] inline LeanBrokerTx
leanLoanBrokerCover(AppliedBrokerTx const& cpp, CoverOp op, std::optional<STAmount> const& amount)
{
    LeanBrokerTx lean;
    switch (op)
    {
        case CoverOp::Deposit:
            lean.can = leanCanCoverDeposit(cpp.pre, cpp.pool, coverAmount(amount));
            break;
        case CoverOp::Withdraw:
            lean.can = leanCanCoverWithdraw(cpp.pre, cpp.pool, coverAmount(amount));
            break;
        case CoverOp::Clawback:
            lean.can = leanCanCoverClawback(cpp.pre, cpp.pool, amount);
            break;
    }
    if (lean.can.leanError || lean.can.ter != tesSUCCESS)
        return lean;
    LeanCoverResult const r = op == CoverOp::Deposit
        ? leanCoverDeposit(cpp.pre, cpp.pool, coverAmount(amount))
        : op == CoverOp::Withdraw ? leanCoverWithdraw(cpp.pre, cpp.pool, coverAmount(amount))
                                  : leanCoverClawback(cpp.pre, cpp.pool, amount);
    lean.leanError = r.leanError;
    lean.error = r.error;
    lean.broker = r.broker;
    lean.amount = Number{r.amount};
    return lean;
}

// Both sides of a broker transaction return `expected`; when both succeed, every broker field is
// equal, the pool is unchanged (the model does not touch it), and the cover the model moved is
// what C++ moved and booked, when the C++ side set them. A model error never matches: a row
// expecting tefEXCEPTION names its model error (expectCppOnlyRejection).
inline void
expectSame(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedBrokerTx const& cpp,
    LeanBrokerTx const& lean,
    TER expected)
{
    // doApply only counts when preclaim accepts.
    std::optional<LeanError> const leanError = lean.can.leanError ? lean.can.leanError
        : lean.can.ter == tesSUCCESS                              ? lean.leanError
                                                                  : std::nullopt;
    TER const leanTer = lean.can.ter != tesSUCCESS ? lean.can.ter : lean.error.value_or(tesSUCCESS);
    suite.expect(
        !leanError && expected != tefEXCEPTION && leanTer == expected && cpp.ter == expected,
        at + "lean=" + leanVerdictText(leanError, leanTer) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected));
    if (leanError || leanTer != tesSUCCESS || cpp.ter != tesSUCCESS)
        return;

    auto const same = [&](char const* field, auto const& l, auto const& c) {
        auto const text = [](auto const& v) {
            if constexpr (std::is_same_v<std::decay_t<decltype(v)>, Number>)
            {
                return to_string(v);
            }
            else
            {
                return std::to_string(v);
            }
        };
        suite.expect(l == c, at + field + " lean=" + text(l) + " cpp=" + text(c));
    };
    LoanBroker const& lb = lean.broker;
    LoanBroker const& cb = cpp.post;
    same("numericType", int{lb.numericType}, int{cb.numericType});
    same("managementFeeRate", lb.managementFeeRate, cb.managementFeeRate);
    same("coverRateMinimum", lb.coverRateMinimum, cb.coverRateMinimum);
    same("coverRateLiquidation", lb.coverRateLiquidation, cb.coverRateLiquidation);
    same("debtTotal", lb.debtTotal, cb.debtTotal);
    same("debtMaximum", lb.debtMaximum, cb.debtMaximum);
    same("coverAvailable", lb.coverAvailable, cb.coverAvailable);
    same("loanCount", lb.loanCount, cb.loanCount);
    expectSameVault(suite, at + "pool ", cpp.pool, cpp.poolAfter);
    if (cpp.moved)
        same("moved", lean.amount.value_or(Number{}), *cpp.moved);
    if (cpp.booked)
        same("booked", lean.amount.value_or(Number{}), *cpp.booked);
}

// C++ returns `expected`, a TER the model has no counterpart for: a preflight rejection (tem) or
// a C++ exception (tefEXCEPTION). Preclaim must not fail with a model error. With a `leanError` the
// model's doApply must fail with exactly that error (notLawful: the fields break a broker
// invariant). With none it must SUCCEED: no model error and no model TER (it cannot express the
// field).
inline void
expectCppOnlyRejection(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedBrokerTx const& cpp,
    LeanBrokerTx const& lean,
    TER expected,
    std::optional<LeanError> leanError)
{
    suite.expect(
        cpp.ter == expected && !lean.can.leanError && lean.leanError == leanError &&
            (leanError || !lean.error),
        at + "lean=" + leanVerdictText(lean.leanError, lean.error.value_or(tesSUCCESS)) +
            " preclaim error " + leanErrorText(lean.can.leanError) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected) + " with lean error " + leanErrorText(leanError));
}

// The model's value of a loan transaction field equals C++'s.
template <class T>
void
expectSameField(
    beast::unit_test::Suite& suite,
    std::string const& at,
    char const* field,
    T const& lean,
    T const& cpp)
{
    auto const text = [](T const& v) {
        if constexpr (std::is_same_v<T, Number>)
        {
            return to_string(v);
        }
        else
        {
            return std::to_string(v);
        }
    };
    suite.expect(lean == cpp, at + field + " lean=" + text(lean) + " cpp=" + text(cpp));
}

// Every field of the model's loan broker equals C++'s.
inline void
expectSameBroker(
    beast::unit_test::Suite& suite,
    std::string const& at,
    LoanBroker const& lb,
    LoanBroker const& cb)
{
    auto const same = [&](char const* field, auto const& l, auto const& c) {
        expectSameField(suite, at, field, l, c);
    };
    same("broker numericType", int{lb.numericType}, int{cb.numericType});
    same("broker managementFeeRate", lb.managementFeeRate, cb.managementFeeRate);
    same("broker coverRateMinimum", lb.coverRateMinimum, cb.coverRateMinimum);
    same("broker coverRateLiquidation", lb.coverRateLiquidation, cb.coverRateLiquidation);
    same("broker debtTotal", lb.debtTotal, cb.debtTotal);
    same("broker debtMaximum", lb.debtMaximum, cb.debtMaximum);
    same("broker coverAvailable", lb.coverAvailable, cb.coverAvailable);
    same("broker loanCount", lb.loanCount, cb.loanCount);
}

// Both sides of a loan transaction return `expected`; when both succeed, every field of the loan
// and of its broker is equal, so is the pool, and so are the amounts the model returns and what
// C++ moved, when the C++ side set them. A model error never matches: a row expecting
// tefEXCEPTION names its model error (expectCppOnlyRejection).
inline void
expectSame(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedLoanTx const& cpp,
    LeanLoanTx const& lean,
    TER expected)
{
    // doApply only counts when preclaim accepts.
    std::optional<LeanError> const leanError = lean.can.leanError ? lean.can.leanError
        : lean.can.ter == tesSUCCESS                              ? lean.result.leanError
                                                                  : std::nullopt;
    TER const leanTer =
        lean.can.ter != tesSUCCESS ? lean.can.ter : lean.result.error.value_or(tesSUCCESS);
    suite.expect(
        !leanError && expected != tefEXCEPTION && leanTer == expected && cpp.ter == expected,
        at + "lean=" + leanVerdictText(leanError, leanTer) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected));
    if (leanError || leanTer != tesSUCCESS || cpp.ter != tesSUCCESS)
        return;

    auto const same = [&](char const* field, auto const& l, auto const& c) {
        expectSameField(suite, at, field, l, c);
    };
    expectSameBroker(suite, at, lean.result.loan.broker, cpp.post.broker);
    Loan const& l = lean.result.loan;
    Loan const& c = cpp.post;
    same("interestRate", l.interestRate, c.interestRate);
    same("lateInterestRate", l.lateInterestRate, c.lateInterestRate);
    same("closeInterestRate", l.closeInterestRate, c.closeInterestRate);
    same("overpaymentInterestRate", l.overpaymentInterestRate, c.overpaymentInterestRate);
    same("overpaymentFee", l.overpaymentFee, c.overpaymentFee);
    same("originationFee", l.originationFee, c.originationFee);
    same("serviceFee", l.serviceFee, c.serviceFee);
    same("latePaymentFee", l.latePaymentFee, c.latePaymentFee);
    same("closePaymentFee", l.closePaymentFee, c.closePaymentFee);
    same("paymentInterval", l.paymentInterval, c.paymentInterval);
    same("paymentTotal", l.paymentTotal, c.paymentTotal);
    same("gracePeriod", l.gracePeriod, c.gracePeriod);
    same("startDate", l.startDate, c.startDate);
    same("paymentRemaining", l.paymentRemaining, c.paymentRemaining);
    same("principalInitial", l.principalInitial, c.principalInitial);
    same("periodicPayment", l.periodicPayment, c.periodicPayment);
    same("principalOutstanding", l.principalOutstanding, c.principalOutstanding);
    same("totalValueOutstanding", l.totalValueOutstanding, c.totalValueOutstanding);
    same("managementFeeOutstanding", l.managementFeeOutstanding, c.managementFeeOutstanding);
    same("loanScale", l.loanScale, c.loanScale);
    same("previousPaymentDueDate", l.previousPaymentDueDate, c.previousPaymentDueDate);
    same("nextPaymentDueDate", l.nextPaymentDueDate, c.nextPaymentDueDate);
    same("isPending", int{l.isPending}, int{c.isPending});
    same("isImpaired", int{l.isImpaired}, int{c.isImpaired});
    same("isDefault", int{l.isDefault}, int{c.isDefault});
    same("allowsOverpayment", int{l.allowsOverpayment}, int{c.allowsOverpayment});
    expectSameVault(suite, at + "pool ", lean.result.pool, cpp.poolAfter);
    if (cpp.toBorrower)
        same("toBorrower", lean.result.amountToBorrower, *cpp.toBorrower);
    if (cpp.toPool)
        same("toPool", lean.result.amountToPool, *cpp.toPool);
    if (cpp.toBroker)
        same("toBroker", lean.result.amountToBroker, *cpp.toBroker);
    // What left the broker's pseudo-account went to the pool.
    if (cpp.fromBroker)
        same("fromBroker", lean.result.amountToPool, *cpp.fromBroker);
}

// C++ returns `expected`, a TER the model has no counterpart for: a preflight rejection (tem) or
// a C++ exception (tefEXCEPTION). Preclaim must not fail with a model error. With a `leanError` the
// model's doApply must fail with exactly that error (notLawful: the fields break a loan
// invariant). With none it must SUCCEED: no model error and no model TER.
inline void
expectCppOnlyRejection(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedLoanTx const& cpp,
    LeanLoanTx const& lean,
    TER expected,
    std::optional<LeanError> leanError)
{
    suite.expect(
        cpp.ter == expected && !lean.can.leanError && lean.result.leanError == leanError &&
            (leanError || !lean.result.error),
        at + "lean=" +
            leanVerdictText(lean.result.leanError, lean.result.error.value_or(tesSUCCESS)) +
            " preclaim error " + leanErrorText(lean.can.leanError) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected) + " with lean error " + leanErrorText(leanError));
}

// The check a list row asks for: a row naming a `leanError` is a C++-only rejection the model
// answers with that error; a row without one expects `expected` on both sides.
template <class Cpp, class Lean>
void
expectRow(
    beast::unit_test::Suite& suite,
    std::string const& at,
    Cpp const& cpp,
    Lean const& lean,
    TER expected,
    std::optional<LeanError> leanError)
{
    if (leanError)
        expectCppOnlyRejection(suite, at, cpp, lean, expected, leanError);
    else
        expectSame(suite, at, cpp, lean, expected);
}

// Both sides of a LoanDelete return `expected`; when both succeed, the loan is gone and every
// field of its broker and of the pool is equal. A model error never matches.
inline void
expectSame(
    beast::unit_test::Suite& suite,
    std::string const& at,
    AppliedLoanTx const& cpp,
    LeanDeleteTx const& lean,
    TER expected)
{
    // doApply only counts when preclaim accepts.
    std::optional<LeanError> const leanError = lean.can.leanError ? lean.can.leanError
        : lean.can.ter == tesSUCCESS                              ? lean.result.leanError
                                                                  : std::nullopt;
    TER const leanTer =
        lean.can.ter != tesSUCCESS ? lean.can.ter : lean.result.error.value_or(tesSUCCESS);
    suite.expect(
        !leanError && expected != tefEXCEPTION && leanTer == expected && cpp.ter == expected,
        at + "lean=" + leanVerdictText(leanError, leanTer) + " cpp=" + transToken(cpp.ter) +
            " expected=" + transToken(expected));
    if (leanError || leanTer != tesSUCCESS || cpp.ter != tesSUCCESS)
        return;

    suite.expect(cpp.erased, at + "the loan is still on the ledger");
    expectSameBroker(suite, at, lean.result.broker, cpp.post.broker);
    expectSameVault(suite, at + "pool ", lean.result.pool, cpp.poolAfter);
}

}  // namespace xrpl::test::formal_verification
