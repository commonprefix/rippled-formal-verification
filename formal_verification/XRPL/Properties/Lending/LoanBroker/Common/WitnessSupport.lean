import XRPL.Properties.Lending.LoanBroker.Common.ReachableDefs
import XRPL.Properties.Vault.Proofs.Support.ReachableHistory

/-! # Shared fixtures for the cover witnesses

A reachable history on a closed-ended IOU vault with base exponent `-6`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

deriving instance DecidableEq for RawLoanBroker

instance : DecidableEq LoanBroker := fun a b =>
  decidable_of_iff (a.toRawLoanBroker = b.toRawLoanBroker)
    ⟨fun h => by obtain ⟨av, _, _⟩ := a; obtain ⟨bv, _, _⟩ := b; cases h; rfl, fun h => by rw [h]⟩

deriving instance DecidableEq for LoanBrokerCoverResult

/-- A closed-ended IOU vault with base exponent `-6`. -/
def wvBase6 : Vault :=
  match Vault.create (some 6) none (some ⟨100, 900000000⟩) none false .fractional with
  | .ok v => v
  | .error _ => Vault.placeholder

/-- A new broker with a DebtMaximum of `1000` and 1% minimum cover. -/
private def wtxCreate : LoanBrokerSetCreate :=
  { debtMaximum := some ⟨false, 1000000000000000000, -15⟩, managementFeeRate := some 100
  , coverRateMinimum := some 1000, coverRateLiquidation := some 1000 }

/-- An empty IOU broker, the result when a run below fails. -/
private def wbFallback : LoanBroker :=
  ⟨{ numericType := .fractional, managementFeeRate := 0, coverRateMinimum := 0, coverRateLiquidation := 0
   , debtTotal := Number.zero, debtMaximum := Number.zero, coverAvailable := Number.zero, loanCount := 0 },
   by native_decide, by native_decide⟩

/-- The result of a successful cover run, or an empty one when the run fails. -/
def wResultOf (x : TerExcept LoanBrokerCoverResult) : LoanBrokerCoverResult :=
  match x.run with
  | .ok (.ok r) => r
  | _ => ⟨STAmount.unchecked .fractional 0 0 false, wbFallback⟩

/-- An IOU amount with mantissa `m` and exponent `e`. -/
def wAmount (m : UInt64) (e : Int) : STAmount := STAmount.unchecked .fractional m e false

/-- The broker `wtxCreate` creates, with no cover. -/
def wbEmpty : LoanBroker :=
  match LoanBroker.create wtxCreate .fractional with
  | .ok lb => lb
  | .error _ => wbFallback

/-- `12.34567890123456` deposited into `wbEmpty` is credited `12.345678`. -/
private def wrHeld : LoanBrokerCoverResult := wResultOf (wbEmpty.coverDeposit wvBase6 (wAmount 1234567890123456 (-14)))

/-- The broker holding `12.345678` of cover. -/
def wbHeld : LoanBroker := wrHeld.loanBroker'

/-- `1.5` base units. -/
def waHalves : STAmount := wAmount 1500000000000000 (-21)

/-- `3` base units, the sum of two `waHalves`. -/
def waThree : STAmount := wAmount 3000000000000000 (-21)

/-- The broker after the deposit is reachable. -/
lemma wbHeld_reachable : wbHeld.Reachable (-6) :=
  ⟨wvBase6, wtxCreate, wbEmpty, by native_decide, by native_decide, by native_decide,
    .coverDeposit wbEmpty wvBase6 (wAmount 1234567890123456 (-14)) wrHeld .refl (by native_decide)
      (by native_decide) (STAmount.canonical_of_canonicalB _ (by native_decide)) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)⟩

end XRPL.Model.Lending
