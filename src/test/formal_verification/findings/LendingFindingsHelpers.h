#pragma once

#include <test/jtx/Env.h>
#include <test/jtx/TestHelpers.h>
#include <test/jtx/fee.h>
#include <test/jtx/sig.h>

#include <xrpl/basics/Number.h>
#include <xrpl/protocol/Indexes.h>
#include <xrpl/protocol/Keylet.h>
#include <xrpl/protocol/Protocol.h>
#include <xrpl/protocol/SField.h>
#include <xrpl/protocol/SeqProxy.h>

namespace xrpl {

// A loan to the fixture's depositor with one payment after 120 s and LateInterestRate 100%.
// `Fixture` is the LendingFixture of the fixed precision test bases.
template <class Fixture>
Keylet
openLoanWithLateInterest(test::jtx::Env& env, Fixture const& fixture, Number const& principal)
{
    using namespace test::jtx;

    Keylet const loanKeylet = keylet::loan(
        fixture.brokerKeylet.key,
        SeqProxy::rawSequence(env.le(fixture.brokerKeylet)->at(sfLoanSequence)));
    env(loan::set(fixture.depositor, fixture.brokerKeylet.key, principal),
        loan::kLateInterestRate(percentageToTenthBips(100)),
        loan::kGracePeriod(60),
        loan::kPaymentInterval(120),
        loan::kPaymentTotal(1),
        Sig(sfCounterpartySignature, fixture.owner),
        Fee(env.current()->fees().base * 2));
    env.close();
    return loanKeylet;
}

}  // namespace xrpl
