import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport

/-! # Witnesses for the clawback theorems

Runs on a reachable broker of a vault with base exponent `-6`, and on lawful brokers off the base grid of a vault
with base exponent `0` that show the Open-zone hypothesis is needed. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- A full clawback from `wbOffGridDebt`. -/
private def wrClawDebt : LoanBrokerCoverResult := wResultOf (wbOffGridDebt.coverClawback wvBase0 none)

/-- Proof body of `coverClawback_keeps_minimum_attained`. -/
lemma LoanBroker.coverClawback_keeps_minimum_witness :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.loanBroker'.toExact.coverAvailable < minimumCover.toRat :=
  ⟨wbOffGridDebt, wvBase0, none, wrClawDebt, ⟨false, 1000000000000000000, -18⟩, by native_decide,
    fun h => absurd h (by native_decide), (fun a ha => by cases ha), by native_decide, by native_decide,
    by native_decide, by native_decide⟩

/-- Proof body of `roundedCoverClawback_all_attained`. -/
lemma LoanBroker.roundedCoverClawback_all_witness :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.amount'.toRat ≠ lb.toExact.coverAvailable - minimumCover.toRat :=
  ⟨wbOffGridDebt, wvBase0, none, wrClawDebt, ⟨false, 1000000000000000000, -18⟩, by native_decide,
    fun h => absurd h (by native_decide), (fun a ha => by cases ha), Or.inl rfl, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Proof body of `roundedCoverClawback_all_leaves_minimum_attained`. -/
lemma LoanBroker.coverClawback_all_leaves_minimum_witness :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount) (res : LoanBrokerCoverResult)
      (minimumCover : Number),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      (amount = none ∨ ∃ a, amount = some a ∧ a.isZero = true) ∧
      minimumBrokerCover lb.numericType lb.debtTotal lb.coverRateMinimum v.baseExponent = .ok minimumCover ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .ok (.ok res) ∧
      res.loanBroker'.toExact.coverAvailable ≠ minimumCover.toRat :=
  ⟨wbOffGridDebt, wvBase0, none, wrClawDebt, ⟨false, 1000000000000000000, -18⟩, by native_decide,
    fun h => absurd h (by native_decide), (fun a ha => by cases ha), Or.inl rfl, by native_decide,
    by native_decide, by native_decide, by native_decide⟩

/-- Proof body of `coverClawback_total_lawful_attained`. -/
lemma LoanBroker.coverClawback_lawful_total_witness :
    ∃ (lb : LoanBroker) (v : Vault) (amount : Option STAmount),
      v.numericType = lb.numericType ∧
      (lb.numericType.isIntegral = true → lb.numericType.maxValue.toNat ≤ maxRep.toNat) ∧
      (∀ a ∈ amount, a.CanonicalOrZero ∧ a.mNumericType = lb.numericType ∧ 0 ≤ a.toRat) ∧
      lb.canCoverClawback v amount = .ok .tesSUCCESS ∧ (lb.coverClawback v amount).run = .error .notLawful :=
  ⟨wbOffGrid, wvBase0, none, by native_decide, fun h => absurd h (by native_decide), (fun a ha => by cases ha),
    by native_decide, by native_decide⟩

/-- `waHalves` clawed from `wbHeld`, then again, and `waThree` at once. -/
private def wrClaw1 : LoanBrokerCoverResult := wResultOf (wbHeld.coverClawback wvBase6 (some waHalves))
private def wrClaw2 : LoanBrokerCoverResult :=
  wResultOf (wrClaw1.loanBroker'.coverClawback wvBase6 (some waHalves))
private def wrClaw3 : LoanBrokerCoverResult := wResultOf (wbHeld.coverClawback wvBase6 (some waThree))

/-- Proof body of `coverClawback_split_attained`. -/
lemma LoanBroker.coverClawback_split_witness :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧
      v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      lb.canCoverClawback v (some a) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some a)).run = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverClawback v (some b) = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverClawback v (some b)).run = .ok (.ok r2) ∧
      lb.canCoverClawback v (some c) = .ok .tesSUCCESS ∧ (lb.coverClawback v (some c)).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  ⟨wbHeld, -6, wvBase6, waHalves, waHalves, waThree, wrClaw1, wrClaw2, wrClaw3, wbHeld_reachable,
    by native_decide, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), STAmount.canonical_of_canonicalB _ (by native_decide),
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.Lending
