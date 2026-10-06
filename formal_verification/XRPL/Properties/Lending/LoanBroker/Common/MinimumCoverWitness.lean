import XRPL.Properties.Lending.LoanBroker.Defs

/-! # Witness for the minimum cover at two vault scales

A broker that meets the minimum cover at one vault scale but not at a coarser one, checked
by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The minimum cover at vault scale `e` is strictly below the one at vault scale `e'`. -/
def minCoverRises (nt : NumericType) (debtTotal : Number) (rate : TenthBips32) (e e' : Int) : Bool :=
  match minimumBrokerCover nt debtTotal rate e, minimumBrokerCover nt debtTotal rate e' with
  | .ok m, .ok m' => decide (m.toRat < m'.toRat)
  | _, _ => false

private lemma minCoverRises_witness :
    minCoverRises .fractional ⟨false, 1234567890123000000, -17⟩ 10000 (-13) 0 = true := by
  native_decide

/-- A debt of `12.34567890123` at `10%` needs `1.234567890123` of cover at vault scale `10^-13`,
but `2` at vault scale `10^0`. -/
lemma minimumBrokerCover_scale_witness :
    ∃ (nt : NumericType) (debtTotal : Number) (rate : TenthBips32) (e e' : Int) (m m' : Number),
      e < e' ∧ -96 ≤ e ∧ e' ≤ 80 ∧ minimumBrokerCover nt debtTotal rate e = .ok m ∧
      minimumBrokerCover nt debtTotal rate e' = .ok m' ∧ m.toRat < m'.toRat := by
  have h := minCoverRises_witness
  unfold minCoverRises at h
  split at h
  · rename_i m m' hm hm'
    exact ⟨_, _, _, -13, 0, m, m', by decide, by decide, by decide, hm, hm', of_decide_eq_true h⟩
  · exact absurd h (by decide)

end XRPL.Model.Lending
