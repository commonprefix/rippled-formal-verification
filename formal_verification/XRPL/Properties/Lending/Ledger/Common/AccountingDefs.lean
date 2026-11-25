import XRPL.Properties.Lending.Ledger.Common.ScaleInv

/-! # Sums of PrincipalOutstanding over the stored loans

`l.principalSum p` adds PrincipalOutstanding over the stored loans `p` selects, such as the pending or
the impaired ones. A loan effect changes the sum by what its slot held before and after. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

/-- PrincipalOutstanding of a slot's loan when `p` selects it, else zero. -/
def LoanEntry.principalIf (p : Loan → Bool) : Option LoanEntry → ℚ
  | some e => if p e.loan then e.loan.principalOutstanding.toRat else 0
  | none => 0

/-- Σ PrincipalOutstanding of the stored loans that `p` selects. -/
def LendingLedger.principalSum (l : LendingLedger) (p : Loan → Bool) : ℚ :=
  (l.loans.map (LoanEntry.principalIf p)).sum

/-- A slot adds at least zero. -/
private lemma LoanEntry.principalIf_nonneg (p : Loan → Bool) (o : Option LoanEntry) :
    0 ≤ LoanEntry.principalIf p o := by
  cases o with
  | none => exact le_refl _
  | some e =>
    simp only [LoanEntry.principalIf]
    split
    · exact (e.loan.exact.principalOutstanding_nonneg : 0 ≤ e.loan.principalOutstanding.toRat)
    · exact le_refl _

/-- A sum of slots is at least zero. -/
lemma LendingLedger.principalSum_nonneg (l : LendingLedger) (p : Loan → Bool) : 0 ≤ l.principalSum p :=
  List.sum_nonneg fun _ hx => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    exact LoanEntry.principalIf_nonneg p o

/-- One slot adds at most the whole sum. -/
lemma LendingLedger.principalIf_le_sum (l : LendingLedger) (p : Loan → Bool) (i : Nat) :
    LoanEntry.principalIf p (l.loan? i) ≤ l.principalSum p := by
  have hnn : ∀ x ∈ l.loans.map (LoanEntry.principalIf p), 0 ≤ x := fun _ hx => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    exact LoanEntry.principalIf_nonneg p o
  unfold LendingLedger.loan?
  cases h : l.loans[i]? with
  | none => exact l.principalSum_nonneg p
  | some o => exact List.single_le_sum hnn _ (List.mem_map_of_mem (List.mem_of_getElem? h))

/-- Rewriting one entry of a list changes its sum by the old and the new entry. -/
lemma List.sum_set_add (xs : List ℚ) (i : Nat) (a : ℚ) (hi : i < xs.length) :
    (xs.set i a).sum + xs[i] = xs.sum + a := by
  induction xs generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.set_cons_zero, List.sum_cons, List.getElem_cons_zero]; ring
    | succ k =>
      simp only [List.set_cons_succ, List.sum_cons, List.getElem_cons_succ]
      have := ih k (by simp at hi; omega)
      linarith

/-- A loan effect changes a sum by its slot. The sum after it, plus what the slot held before, is the
sum before plus what the effect writes. -/
lemma LendingLedger.principalSum_commitLoan (l : LendingLedger) (u : LoanEffect) (p : Loan → Bool) :
    (l.commitLoan u).principalSum p + LoanEntry.principalIf p (l.loan? u.loanIndex) =
      l.principalSum p + LoanEntry.principalIf p u.loan := by
  unfold LendingLedger.principalSum LendingLedger.commitLoan LendingLedger.loan? storeSlot
  dsimp only
  split
  · rename_i hi
    rw [List.map_set, List.getElem?_eq_getElem hi, Option.join_some]
    have := List.sum_set_add (l.loans.map (LoanEntry.principalIf p)) u.loanIndex (LoanEntry.principalIf p u.loan)
      (by simpa using hi)
    simpa using this
  · rename_i hi
    rw [List.getElem?_eq_none (by omega), List.map_append, List.sum_append]
    simp [LoanEntry.principalIf]

/-- A ledger with the same loans has the same sums. -/
lemma LendingLedger.principalSum_of_loans {l l' : LendingLedger} (h : l'.loans = l.loans) (p : Loan → Bool) :
    l'.principalSum p = l.principalSum p := by
  unfold LendingLedger.principalSum; rw [h]

/-- A stored loan's PrincipalOutstanding is a whole number of the vault's base units. -/
lemma LendingLedger.ScaleInv.principal_grid {l : LendingLedger} (hinv : l.ScaleInv) {j : Nat} {e : LoanEntry}
    (he : l.loan? j = some e) :
    ∃ m : ℕ, e.loan.principalOutstanding.toRat = (m : ℚ) * 10 ^ l.vault.baseExponent := by
  obtain ⟨m, -, hm⟩ := e.loan.grid.principalOutstanding_atExponent
  simp only [RawLoan.toExact] at hm
  rw [hinv.loanScale j e he] at hm
  exact ⟨m, hm⟩

/-- The sums are on the base grid. Every sum of stored loans is a whole number of base units. -/
lemma LendingLedger.ScaleInv.principalSum_grid {l : LendingLedger} (hinv : l.ScaleInv) (p : Loan → Bool) :
    ∃ n : ℕ, l.principalSum p = (n : ℚ) * 10 ^ l.vault.baseExponent := by
  have hslot : ∀ o ∈ l.loans, ∃ m : ℕ, LoanEntry.principalIf p o = (m : ℚ) * 10 ^ l.vault.baseExponent := by
    intro o ho
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ho
    cases o with
    | none => exact ⟨0, by simp [LoanEntry.principalIf]⟩
    | some e =>
      have he : l.loan? j = some e := by unfold LendingLedger.loan?; rw [hj]; rfl
      obtain ⟨m, hm⟩ := hinv.principal_grid he
      simp only [LoanEntry.principalIf]
      split
      · exact ⟨m, hm⟩
      · exact ⟨0, by simp⟩
  unfold LendingLedger.principalSum
  generalize l.loans = xs at hslot
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons o os ih =>
    obtain ⟨m, hm⟩ := hslot o List.mem_cons_self
    obtain ⟨n, hn⟩ := ih fun o' ho' => hslot o' (List.mem_cons_of_mem _ ho')
    exact ⟨m + n, by rw [List.map_cons, List.sum_cons, hm, hn]; push_cast; ring⟩

end XRPL.Model.Lending
