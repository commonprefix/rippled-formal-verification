#pragma once

#include <test/jtx/Account.h>
#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/fee.h>
#include <test/jtx/sig.h>

#include <xrpl/basics/Number.h>
#include <xrpl/basics/chrono.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/SeqProxy.h>
#include <xrpl/protocol/Units.h>

#include <cstdint>

namespace xrpl {

// A loan to the fixture's depositor at LateInterestRate 100%, the maximum. `Fixture` is the
// LendingFixture of the fixed precision test bases.
template <class Fixture>
Keylet
openLoanWithLateInterest(
    test::jtx::Env& env,
    Fixture const& fixture,
    Number const& principal,
    std::uint32_t paymentTotal = 1,
    std::uint32_t paymentInterval = 120)
{
    using namespace test::jtx;

    Keylet const loanKeylet = keylet::loan(
        fixture.brokerKeylet.key,
        SeqProxy::rawSequence(env.le(fixture.brokerKeylet)->at(sfLoanSequence)));
    env(loan::set(fixture.depositor, fixture.brokerKeylet.key, principal),
        loan::kLateInterestRate(percentageToTenthBips(100)),
        loan::kGracePeriod(60),
        loan::kPaymentInterval(paymentInterval),
        loan::kPaymentTotal(paymentTotal),
        Sig(sfCounterpartySignature, fixture.owner),
        Fee(env.current()->fees().base * 2));
    env.close();
    return loanKeylet;
}

// A two-step loan from the fixture's owner to `borrower`, pending until the borrower accepts it.
template <class Fixture>
Keylet
proposeLoan(
    test::jtx::Env& env,
    Fixture const& fixture,
    test::jtx::Account const& borrower,
    Number const& principal,
    NetClock::time_point startDate,
    std::uint32_t paymentInterval,
    TenthBips32 interestRate = TenthBips32{0})
{
    using namespace test::jtx;

    Keylet const& broker = fixture.brokerKeylet;
    Keylet const loanKeylet =
        keylet::loan(broker.key, SeqProxy::rawSequence(env.le(broker)->at(sfLoanSequence)));
    env(loan::set(fixture.owner, broker.key, principal),
        loan::kBorrower(borrower),
        loan::kStartDate(startDate.time_since_epoch().count()),
        loan::kInterestRate(interestRate),
        loan::kPaymentInterval(paymentInterval));
    env.close();
    return loanKeylet;
}

// The same loan to the fixture's depositor.
template <class Fixture>
Keylet
proposeLoan(
    test::jtx::Env& env,
    Fixture const& fixture,
    Number const& principal,
    NetClock::time_point startDate,
    std::uint32_t paymentInterval,
    TenthBips32 interestRate = TenthBips32{0})
{
    return proposeLoan(
        env, fixture, fixture.depositor, principal, startDate, paymentInterval, interestRate);
}

}  // namespace xrpl
