import XRPL.Properties.Lending.LoanBroker.Common.WitnessSupport

/-! # Witnesses for the withdrawal theorems

A run on a reachable broker of a vault with base exponent `-6`. Two withdrawals of `1.5` base units
pay out one base unit each, while one withdrawal of `3` pays out all three. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- `waHalves` withdrawn from `wbHeld`, then again, and `waThree` at once. -/
private def wrWd1 : LoanBrokerCoverResult := wResultOf (wbHeld.coverWithdraw wvBase6 waHalves)
private def wrWd2 : LoanBrokerCoverResult := wResultOf (wrWd1.loanBroker'.coverWithdraw wvBase6 waHalves)
private def wrWd3 : LoanBrokerCoverResult := wResultOf (wbHeld.coverWithdraw wvBase6 waThree)

/-- Proof body of `cover_split_withdraw_attained`. -/
lemma LoanBroker.coverWithdraw_split_witness :
    ∃ (lb : LoanBroker) (base : Int) (v : Vault) (a b c : STAmount) (r1 r2 s : LoanBrokerCoverResult),
      lb.Reachable base ∧
      v.baseExponent = base ∧ v.numericType = lb.numericType ∧
      a.Canonical ∧ b.Canonical ∧ c.Canonical ∧
      a.mNumericType = lb.numericType ∧ b.mNumericType = lb.numericType ∧ c.mNumericType = lb.numericType ∧
      0 < a.toRat ∧ 0 < b.toRat ∧ c.toRat = a.toRat + b.toRat ∧
      lb.canCoverWithdraw v a = .ok .tesSUCCESS ∧ (lb.coverWithdraw v a).run = .ok (.ok r1) ∧
      r1.loanBroker'.canCoverWithdraw v b = .ok .tesSUCCESS ∧
      (r1.loanBroker'.coverWithdraw v b).run = .ok (.ok r2) ∧
      lb.canCoverWithdraw v c = .ok .tesSUCCESS ∧ (lb.coverWithdraw v c).run = .ok (.ok s) ∧
      r2.loanBroker'.toExact.coverAvailable ≠ s.loanBroker'.toExact.coverAvailable :=
  ⟨wbHeld, -6, wvBase6, waHalves, waHalves, waThree, wrWd1, wrWd2, wrWd3, wbHeld_reachable,
    by native_decide, by native_decide,
    STAmount.canonical_of_canonicalB _ (by native_decide), STAmount.canonical_of_canonicalB _ (by native_decide),
    STAmount.canonical_of_canonicalB _ (by native_decide), by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.Lending
