import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport

/-! # Witness for a cover deposit above the XRP range

The check's result is computed by the model and checked by `native_decide`. The broker comes from a reachable
history on a closed-ended XRP vault: a create, then a deposit of 1 drop.

A deposit of `10^17` drops takes CoverAvailable to `10^17 + 1` drops, one drop above the largest XRP amount. The
check reads the scale of that sum as an XRP amount, so it ends in an error before it compares with the Open limit. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending.DepositRangeWit

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A closed-ended XRP vault. -/
def vXrp : Vault :=
  match Vault.create none none (some ⟨100, 900000000⟩) none false .native with
  | .ok v => v
  | .error _ => Vault.placeholder

/-- A new broker with no DebtMaximum, no fee and no cover requirement. -/
def txCreate : LoanBrokerSetCreate :=
  { debtMaximum := none, managementFeeRate := none, coverRateMinimum := none, coverRateLiquidation := none }

/-- An empty XRP broker, the result when a run below fails. -/
def bFallback : LoanBroker :=
  ⟨{ numericType := .native, managementFeeRate := 0, coverRateMinimum := 0, coverRateLiquidation := 0
   , debtTotal := Number.zero, debtMaximum := Number.zero, coverAvailable := Number.zero, loanCount := 0 },
   by native_decide, by native_decide⟩

/-- The broker `txCreate` creates, with no cover. -/
def bEmpty : LoanBroker :=
  match LoanBroker.create txCreate .native with
  | .ok lb => lb
  | .error _ => bFallback

/-- An XRP amount of `n` drops. -/
def drops (n : UInt64) : STAmount := STAmount.unchecked .native n 0 false

/-- The deposit of 1 drop into `bEmpty`. -/
def rHeld : LoanBrokerCoverResult :=
  match (bEmpty.coverDeposit vXrp (drops 1)).run with
  | .ok (.ok r) => r
  | _ => ⟨drops 0, bFallback⟩

/-- The broker holding 1 drop of cover. -/
def bHeld : LoanBroker := rHeld.loanBroker'

lemma bHeld_reachable : bHeld.Reachable 0 :=
  ⟨vXrp, txCreate, bEmpty, by native_decide, by native_decide, by native_decide,
    .coverDeposit bEmpty vXrp (drops 1) rHeld .refl (by native_decide)
      (by native_decide) (STAmount.canonical_of_canonicalB _ (by native_decide)) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)⟩

end XRPL.Model.Lending.DepositRangeWit

namespace XRPL.Model.Lending

open XRPL.Model.Protocol DepositRangeWit
open XRPL.Model.SingleAssetVault (Vault)

/-- Cover deposit on a reachable XRP broker that takes CoverAvailable above the largest XRP amount -> the check ends
in an error, not a result code. -/
lemma LoanBroker.canCoverDeposit_out_of_range_witness :
    ∃ (lb : LoanBroker) (v : Vault) (amount : STAmount),
      lb.Reachable v.baseExponent ∧ v.numericType = lb.numericType ∧ amount.Canonical ∧
      amount.mNumericType = lb.numericType ∧ 0 < amount.toRat ∧
      lb.canCoverDeposit v amount = .error .outOfRange :=
  ⟨bHeld, vXrp, drops 100000000000000000, by
      have h : vXrp.baseExponent = 0 := by native_decide
      rw [h]; exact bHeld_reachable,
    by native_decide, STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide,
    by native_decide⟩

end XRPL.Model.Lending
