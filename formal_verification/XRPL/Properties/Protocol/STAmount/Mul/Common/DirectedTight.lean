import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangePos
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.GridNeighbors

/-! # Directed IOU re-rounding onto the 16-digit grid

`STAmount.ofNumber` of a non-negative 19-digit `Number` in a directed mode lands on the 16-digit grid. -/

namespace XRPL.Model.Protocol

/-- Raw `ofNumber` snap facts for a non-negative 19-digit `Number` `r`. Exposes the `normalizeToRange` output
`(mant, exp)`, the grid form of `result`, and the exponent range. -/
lemma STAmount.ofNumber_iou_snap_pos (nt : NumericType) (r : Number) (mode : rounding_mode)
    (result : STAmount)
    (hnt : nt = .fractional)
    (hr_neg : r.negative_ = false)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r mode = .ok result) (hresult : result.mValue ≠ 0) :
    ∃ (mant : Int64) (exp : ℤ),
      r.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) ∧
      result.toRat = (mant.toInt : ℚ) * 10 ^ exp ∧
      result.exponent = exp ∧
      (mant.toInt : ℚ) = ((mant.toUInt64.toNat : ℕ) : ℚ) ∧
      10 ^ 15 ≤ mant.toUInt64.toNat ∧ mant.toUInt64.toNat < 10 ^ 16 ∧
      (-96 : ℤ) ≤ exp ∧ exp ≤ 80 := by
  subst hnt
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
  have hmne : (r.mantissa_ != 0) = true := by simp [hr_ne]
  have hneg_eq : decide (r.signum < 0) = r.negative_ := by
    unfold Number.signum
    rcases hrn : r.negative_ with _ | _ <;> simp only [hmne, if_true, if_false,
      Bool.false_eq_true] <;> decide
  set neg : Bool := decide (r.signum < 0) with hneg_def
  have hneg_false : neg = false := by rw [hneg_eq]; exact hr_neg
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_eq : working = r := by rw [hw_def, hneg_false]; simp
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_eq]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_eq]; exact hr_hi
  have hwe_lo : minExponent ≤ working.exponent_ + 3 := by rw [hw_eq]; omega
  have hwe_hi : working.exponent_ + 4 ≤ maxExponent := by rw [hw_eq]; exact hre_hi
  have hw_neg : working.negative_ = false := by rw [hw_eq]; exact hr_neg
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hbound := normalizeToRange_16_within_ulp working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hmrange := normalizeToRange_16_mantissa_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have herange := normalizeToRange_16_exp_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
    have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
    have hwlarge : (10 : ℚ) ^ (working.exponent_ + 18) ≤ working.toRat := by
      rw [Number.toRat_of_nonneg working hw_neg]
      have h1018 : (10 : ℚ) ^ (18 : ℤ) ≤ (working.mantissa_.toNat : ℚ) := by
        have : ((10 ^ 18 : ℕ) : ℚ) ≤ (working.mantissa_.toNat : ℚ) := by exact_mod_cast hw_lo
        rwa [show ((10 ^ 18 : ℕ) : ℚ) = (10 : ℚ) ^ (18 : ℤ) by push_cast; norm_num] at this
      calc (10 : ℚ) ^ (working.exponent_ + 18)
          = (10 : ℚ) ^ (18 : ℤ) * (10 : ℚ) ^ working.exponent_ := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
        _ ≤ (working.mantissa_.toNat : ℚ) * (10 : ℚ) ^ working.exponent_ := by gcongr
    have hmant_pos : 0 ≤ mant.toInt := by
      by_contra hc
      push Not at hc
      have hmant_neg_q : (mant.toInt : ℚ) < 0 := by exact_mod_cast hc
      have hval_neg : (mant.toInt : ℚ) * 10 ^ exp < 0 :=
        mul_neg_of_neg_of_pos hmant_neg_q (zpow_pos (by norm_num) _)
      have hb := abs_le.mp hbound
      have hule : (10 : ℚ) ^ (working.exponent_ + 3) ≤ (10 : ℚ) ^ (working.exponent_ + 18) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : working.toRat ≤ (mant.toInt : ℚ) * 10 ^ exp + 10 ^ (working.exponent_ + 3) := by
        linarith [hb.1]
      nlinarith [hwlarge, hule, hval_neg]
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      have := hmrange.1; rw [hcMin] at this; omega
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      have := hmrange.2; rw [hcMax] at this; omega
    have hwe : working.exponent_ = r.exponent_ := by rw [hw_eq]
    rw [hwe] at herange
    obtain ⟨v, hv, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hv
    have hcc := STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg mode rfl
      hmtu_lo hmtu_hi (by omega) (by omega) result hok hresult
    obtain ⟨hexp_lo, hexp_hi, hres_eq⟩ := hcc
    have hres_toRat : result.toRat = (mant.toInt : ℚ) * 10 ^ exp := by
      rw [hres_eq, STAmount.toRat_signed]
      show (if neg then (-1 : ℚ) else 1) * (mant.toUInt64.toNat : ℚ) * 10 ^ exp = _
      have : (mant.toUInt64.toNat : ℚ) = (mant.toInt : ℚ) := by
        exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos
      rw [this, hneg_false]; simp
    refine ⟨mant, exp, by rw [← hw_eq]; exact hnorm', hres_toRat, ?_,
      by symm; exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos, hmtu_lo, hmtu_hi, hexp_lo, hexp_hi⟩
    rw [hres_eq]; rfl

end XRPL.Model.Protocol
