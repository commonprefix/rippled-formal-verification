import XRPL.Properties.Lending.LoanBroker.Common.CoverReduction
import XRPL.Properties.Lending.Common.SumRounding

/-! # The credit of a cover deposit

A deposit floors `coverAvailable` plus the amount onto the grid of the sum and credits the
difference. The credit never exceeds the amount and converts back to a `Number` exactly. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A fractional credit floored onto the posterior grid is canonical or zero. -/
lemma sumRoundAndSubtract_frac_fczr (A c : Number) (e : Int) (mode : rounding_mode) (st : STAmount)
    (h : sumRoundAndSubtract A c e .fractional mode = .ok st) : st.FracCanonZero := by
  unfold sumRoundAndSubtract at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨d, -, h⟩ := bind_ok_peel _ _ _ h
  exact STAmount.ofNumber_fractional_fczr d _ st h

variable {α : Type} [AssetPool α]

/-- A deposit never credits more than the amount, and the credit converts back to a `Number` of the
same value. -/
lemma LoanBroker.roundedCoverAmount_le (lb : LoanBroker) (pool : α) (amount r : STAmount)
    (hc : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (hb : (-96 : ℤ) ≤ AssetPool.baseExponent pool ∧ AssetPool.baseExponent pool ≤ 80)
    (hok : (lb.roundedCoverAmount pool amount).run = .ok (.ok r)) :
    r.toRat ≤ amount.toRat ∧
      ∀ m, r.toNumber .to_nearest = .ok m → m.toRat = r.toRat ∧ m.isNormalized := by
  obtain ⟨aN, hnum, hs, -⟩ := LoanBroker.roundedCoverAmount_ok lb pool amount r hok
  obtain ⟨hv, hn⟩ := STAmount.CanonicalOrZero.toNumber_exact (Or.inl hc) aN hnum
  rw [← hv]
  exact sumRoundAndSubtract_downward_le _ _ _ _ r lb.wf.coverAvailable_norm lb.exact.coverAvailable_nonneg hn
    (by rw [hv]; exact hnn) hb hs

end XRPL.Model.Lending
