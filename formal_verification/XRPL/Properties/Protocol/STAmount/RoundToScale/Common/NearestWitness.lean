import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing

/-! # Witnesses that rounding to a scale in ToNearest can end more than half a step away

The IOU addition inside `roundToExponent` rounds twice, so the result can be the farther neighbour (FV_M1_21). -/

namespace XRPL.Model.Protocol

/-- `1.499999999999999` and `2.500000000000001` are canonical IOU amounts. -/
lemma STAmount.roundToExponent_nearest_witness_canonical (m : UInt64) (hlo : 10 ^ 15 ≤ m.toNat)
    (hhi : m.toNat < 10 ^ 16) : (⟨.fractional, m, -15, false⟩ : STAmount).IOUCanonical :=
  ⟨rfl, hlo, hhi, by norm_num, by norm_num⟩

/-- `1.499999999999999` rounded to exponent 0 in ToNearest gives `2`. -/
lemma STAmount.roundToExponent_nearest_up_witness :
    STAmount.roundToExponent ⟨.fractional, 1499999999999999, -15, false⟩ 0 .to_nearest
      = .ok ⟨.fractional, 2000000000000000, -15, false⟩ := by
  decide +kernel

/-- `2.500000000000001` rounded to exponent 0 in ToNearest gives `2`. -/
lemma STAmount.roundToExponent_nearest_down_witness :
    STAmount.roundToExponent ⟨.fractional, 2500000000000001, -15, false⟩ 0 .to_nearest
      = .ok ⟨.fractional, 2000000000000000, -15, false⟩ := by
  decide +kernel

/-- `2` is `0.500000000000001` away from `1.499999999999999`. -/
lemma STAmount.roundToExponent_nearest_up_witness_gap :
    (10 : ℚ) ^ (0 : ℤ) / 2 < |(⟨.fractional, 2000000000000000, -15, false⟩ : STAmount).toRat -
      (⟨.fractional, 1499999999999999, -15, false⟩ : STAmount).toRat| := by
  have hr : (⟨.fractional, 2000000000000000, -15, false⟩ : STAmount).toRat = 2 := by decide +kernel
  have hv : (⟨.fractional, 1499999999999999, -15, false⟩ : STAmount).toRat = 1499999999999999 / 10 ^ 15 := by
    decide +kernel
  rw [hr, hv]
  norm_num [abs_of_pos]

/-- `2` is `0.500000000000001` away from `2.500000000000001`. -/
lemma STAmount.roundToExponent_nearest_down_witness_gap :
    (10 : ℚ) ^ (0 : ℤ) / 2 < |(⟨.fractional, 2000000000000000, -15, false⟩ : STAmount).toRat -
      (⟨.fractional, 2500000000000001, -15, false⟩ : STAmount).toRat| := by
  have hr : (⟨.fractional, 2000000000000000, -15, false⟩ : STAmount).toRat = 2 := by decide +kernel
  have hv : (⟨.fractional, 2500000000000001, -15, false⟩ : STAmount).toRat = 2500000000000001 / 10 ^ 15 := by
    decide +kernel
  rw [hr, hv]
  norm_num [abs_of_neg]

end XRPL.Model.Protocol
