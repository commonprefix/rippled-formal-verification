import XRPL.Properties.Lending.Ledger.Common.LossInv

/-! # Sums over the stored loans

A sum over the loans a predicate selects is zero when it selects none of them. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- No stored loan selected -> the sum is zero. -/
lemma LendingLedger.principalSum_eq_zero (l : LendingLedger) (p : Loan → Bool)
    (h : ∀ (j : Nat) (e : LoanEntry), l.loan? j = some e → p e.loan = false) : l.principalSum p = 0 := by
  unfold LendingLedger.principalSum
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
  cases o with
  | none => rfl
  | some e =>
    obtain ⟨j, hj, hjo⟩ := List.getElem_of_mem ho
    have he : l.loan? j = some e := by
      unfold LendingLedger.loan?; rw [List.getElem?_eq_getElem hj, hjo]; rfl
    simp [LoanEntry.principalIf, h j e he]

end XRPL.Model.Lending
