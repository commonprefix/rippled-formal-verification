import XRPL.Properties.Lending.Ledger.Defs

/-! # The liquidation cap of a default

A default's cover is min(liquidationAmount, PrincipalOutstanding, CoverAvailable), with the liquidation amount
computed from the broker's DebtTotal before the default. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The default of loan `i` on `l` is not capped by its liquidation amount: the liquidation amount it computes from
its broker's DebtTotal is at least min(PrincipalOutstanding, CoverAvailable). -/
def LendingLedger.DefaultUncapped (l : LendingLedger) (i : Nat) : Prop :=
  ∀ (loan : Loan) (minimumCover liquidationAmount : Number), l.LoanAt i loan →
    tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward = .ok minimumCover →
    tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward = .ok liquidationAmount →
    min loan.principalOutstanding.toRat loan.broker.coverAvailable.toRat ≤ liquidationAmount.toRat

end XRPL.Model.Lending
