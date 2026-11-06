import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport

/-! # Witnesses for the deposit theorems

Two deposits of `1.5` base units are credited one each, while one deposit of `3` is credited whole. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- `waHalves` deposited into `wbHeld`, then again, and `waThree` at once. -/
private def wrDep1 : LoanBrokerCoverResult := wResultOf (wbHeld.coverDeposit wvBase6 waHalves)
private def wrDep2 : LoanBrokerCoverResult := wResultOf (wrDep1.loanBroker'.coverDeposit wvBase6 waHalves)
private def wrDep3 : LoanBrokerCoverResult := wResultOf (wbHeld.coverDeposit wvBase6 waThree)

/-- Proof body of `coverDeposit_split_attained`. -/
lemma LoanBroker.coverDeposit_split_witness :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧
      v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + a.toRat ≤ lb.numericType.maxValue.toNat) ∧
      lb.canCoverDeposit v a = .ok .tesSUCCESS ∧ (lb.coverDeposit v a).run = .ok (.ok r1) ∧
      (lb.numericType.isIntegral = true →
        r1.loanBroker'.toExact.coverAvailable + b.toRat ≤ lb.numericType.maxValue.toNat) ∧
      r1.loanBroker'.canCoverDeposit v b = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverDeposit v b).run = .ok (.ok r2) ∧
      (lb.numericType.isIntegral = true →
        lb.toExact.coverAvailable + c.toRat ≤ lb.numericType.maxValue.toNat) ∧
      lb.canCoverDeposit v c = .ok .tesSUCCESS ∧ (lb.coverDeposit v c).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  ⟨wbHeld, -6, wvBase6, waHalves, waHalves, waThree, wrDep1, wrDep2, wrDep3, wbHeld_reachable,
    by native_decide, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), STAmount.canonical_of_canonicalB _ (by native_decide),
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, fun h => absurd h (by native_decide), by native_decide,
    by native_decide, fun h => absurd h (by native_decide), by native_decide, by native_decide,
    fun h => absurd h (by native_decide), by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.Lending
