import XRPL.Properties.Lending.LoanBroker.Defs

/-! # Witness for the minimum cover at two vault scales

A debt whose minimum cover is strictly larger at a coarser vault scale, checked by `native_decide`. -/

set_option linter.style.nativeDecide false

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- A debt of `12.34567890123`. -/
private def wDebt : Number := ⟨false, 1234567890123000000, -17⟩

/-- The minimum cover of `wDebt` at `10%` and vault scale `10^e`, or zero when it fails. -/
private def wMinCover (e : Int) : Number :=
  match minimumBrokerCover .fractional wDebt 10000 e with
  | .ok m => m
  | .error _ => Number.zero

/-- A debt of `12.34567890123` at `10%` needs `1.234567890123` of cover at vault scale `10^-13`,
but `2` at vault scale `10^0`. -/
lemma minimumBrokerCover_scale_witness :
    ∃ (nt : NumericType) (debtTotal : Number) (rate : TenthBips32) (e e' : Int) (m m' : Number),
      e < e' ∧ -96 ≤ e ∧ e' ≤ 80 ∧ minimumBrokerCover nt debtTotal rate e = .ok m ∧
      minimumBrokerCover nt debtTotal rate e' = .ok m' ∧ m ≠ Number.zero ∧ m' ≠ Number.zero ∧ m.toRat < m'.toRat :=
  ⟨.fractional, wDebt, 10000, -13, 0, wMinCover (-13), wMinCover 0, by decide, by decide, by decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

end XRPL.Model.Lending
