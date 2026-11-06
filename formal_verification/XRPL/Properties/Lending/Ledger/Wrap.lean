import XRPL.Properties.Lending.Ledger.Common.WrapLedger

/-! # No transaction wraps a fixed-width integer around

The model checks the fixed-width additions, subtractions and narrowing conversions the lending transactions run,
and stops with `Error.wrap` where C++ wraps around. On a reachable ledger none of them fires. -/

namespace XRPL.Model

open XRPL.Model.Protocol
open XRPL.Model.Lending

variable (l : LendingLedger)

/-- All lending transactions on a reachable ledger -> no fixed-width integer wraps around. -/
theorem Lending.Reachable.transactions_no_wrap (hr : l.Reachable) (tx : LendingTx)
    -- LoanCount does not wrap. C++ LoanSequence stops a broker before `2^32` loans
    (hcount : ∀ (j : Nat) (b : LoanBroker), l.broker? j = some b → b.loanCount + 1 ≠ 0) :
    (l.apply tx).run ≠ .error .wrap :=
  LendingLedger.apply_ne_wrap l hr tx fun j b hb => UInt32.toNat_add_one_lt (hcount j b hb)

end XRPL.Model
