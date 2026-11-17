import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Add.RoundsWithin
import XRPL.Properties.Protocol.Number.Add.Common.Rounded
import XRPL.Properties.Protocol.Number.Add.Common.SameSignDecompose
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport

/-! # Underflow of `IOUAmount` results

An `IOUAmount` constructor or sum returns zero only when the exact value is below `10⁻⁸¹` in magnitude.
`10⁻⁸¹` is the smallest positive `IOUAmount`, mantissa `10^15` at exponent `-96`. -/

namespace XRPL.Model.Protocol

/-- A rounded result is at least any `Number` at or below the exact value, in every mode. -/
private lemma Number.roundsToRepresentable_ge_anyMode (d : Number) (truth : ℚ) (mode : rounding_mode)
    (hR : d.RoundsToRepresentable truth mode) (w : Number) (hw : w.isNormalized)
    (hwt : w.toRat ≤ truth) : w.toRat ≤ d.toRat := by
  cases mode with
  | to_nearest => exact Number.roundsToRepresentable_ge d truth hR w hw hwt
  | upward =>
    obtain ⟨n, hn, hd⟩ := hR
    rw [hd]
    exact hwt.trans (Number.le_upper truth n hn)
  | downward =>
    obtain ⟨n, hn, hd⟩ := hR
    rw [hd]
    exact Number.lower_tight truth n hn w hw hwt
  | towards_zero =>
    obtain ⟨n, hn, hd⟩ := hR
    rw [hd]
    by_cases h0 : truth ≥ 0
    · rw [if_pos h0] at hn
      exact Number.lower_tight truth n hn w hw hwt
    · rw [if_neg h0] at hn
      exact hwt.trans (Number.le_upper truth n hn)

/-- A rounded result is at most any `Number` at or above the exact value, in every mode. -/
private lemma Number.roundsToRepresentable_le_anyMode (d : Number) (truth : ℚ) (mode : rounding_mode)
    (hR : d.RoundsToRepresentable truth mode) (w : Number) (hw : w.isNormalized)
    (hwt : truth ≤ w.toRat) : d.toRat ≤ w.toRat := by
  cases mode with
  | to_nearest => exact Number.roundsToRepresentable_le d truth hR w hw hwt
  | upward =>
    obtain ⟨n, hn, hd⟩ := hR
    rw [hd]
    exact Number.upper_tight truth n hn w hw hwt
  | downward =>
    obtain ⟨n, hn, hd⟩ := hR
    rw [hd]
    exact (Number.lower_le truth n hn).trans hwt
  | towards_zero =>
    obtain ⟨n, hn, hd⟩ := hR
    rw [hd]
    by_cases h0 : truth ≥ 0
    · rw [if_pos h0] at hn
      exact (Number.lower_le truth n hn).trans hwt
    · rw [if_neg h0] at hn
      exact Number.upper_tight truth n hn w hw hwt

/-- A nonzero sum of normalized Numbers is a neighbouring `Number` of the exact sum, in every mode. -/
private lemma Number.operator_add_rounded_anyMode (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y mode = .ok result) (hresult : result.mantissa_ ≠ 0) :
    result.RoundsToRepresentable (x.toRat + y.toRat) mode := by
  cases mode with
  | to_nearest => exact Number.operator_add_rounded_to_nearest x y result hx hy hok
  | upward => exact Number.operator_add_rounded_upward x y result hx hy hok hresult
  | downward => exact Number.operator_add_rounded_downward x y result hx hy hok hresult
  | towards_zero => exact Number.operator_add_rounded_towards_zero x y result hx hy hok

/-- The smallest positive `Number`, `10^18 · 10^minExponent`, is far below `10⁻⁸¹`. -/
private lemma Number.min_positive_le_iou_min :
    (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) ≤ (10 : ℚ) ^ (-81 : ℤ) := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
  exact zpow_le_zpow_right₀ (by norm_num) (by have hm : minExponent = -32768 := rfl; omega)

/-- A `Number` sum whose exact value is at least `10⁻⁸¹` in magnitude is nonzero and at least `10⁻⁸¹` in
magnitude, since `10⁻⁸¹` is itself a `Number`. -/
private lemma Number.operator_add_abs_ge_iou_min (x y sum : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_add x y mode = .ok sum)
    (hbig : (10 : ℚ) ^ (-81 : ℤ) ≤ |x.toRat + y.toRat|) :
    ¬ x.operator_eq y.operator_neg ∧ sum.mantissa_ ≠ 0 ∧ (10 : ℚ) ^ (-81 : ℤ) ≤ |sum.toRat| := by
  have hpos : (0 : ℚ) < (10 : ℚ) ^ (-81 : ℤ) := zpow_pos (by norm_num) _
  have h_no_cancel : ¬ x.operator_eq y.operator_neg := by
    intro hc
    rw [add_truth_zero_of_eq_neg x y hc, abs_zero] at hbig
    linarith
  have hsum_ne : sum.mantissa_ ≠ 0 := by
    by_cases hs : x.negative_ = y.negative_
    · obtain ⟨_, _, _, _, _, hspec⟩ :=
        Number.operator_add_algorithmic_facts_same_sign_anyMode x y sum mode hx hy
          hx_mant_ne hy_mant_ne hs h_no_cancel hok
      exact hspec.result_mant_ne
    · intro h0
      have hsmall := Number.operator_add_underflow_truth_small_proof x y sum mode hx hy
        hx_mant_ne hy_mant_ne hs h_no_cancel hok h0
      linarith [Number.min_positive_le_iou_min]
  refine ⟨h_no_cancel, hsum_ne, ?_⟩
  have hR := Number.operator_add_rounded_anyMode x y sum mode hx hy hok hsum_ne
  have hrange : minExponent + 18 ≤ (-81 : ℤ) ∧ (-81 : ℤ) ≤ maxExponent - 1 := by
    have hm : minExponent = -32768 := rfl
    have hM : maxExponent = 32768 := rfl
    omega
  by_cases h0 : 0 ≤ x.toRat + y.toRat
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow 1 (-81) (by norm_num) hrange
    have hwv' : w.toRat = (10 : ℚ) ^ (-81 : ℤ) := by rw [hwv]; norm_num
    rw [abs_of_nonneg h0] at hbig
    have hge := Number.roundsToRepresentable_ge_anyMode sum _ mode hR w hw (by rw [hwv']; exact hbig)
    rw [hwv'] at hge
    exact hge.trans (le_abs_self _)
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-1) (-81) (by norm_num) hrange
    have hwv' : w.toRat = -(10 : ℚ) ^ (-81 : ℤ) := by rw [hwv]; norm_num
    rw [abs_of_neg (not_le.mp h0)] at hbig
    have hle := Number.roundsToRepresentable_le_anyMode sum _ mode hR w hw (by rw [hwv']; linarith)
    rw [hwv'] at hle
    have hneg := neg_le_abs sum.toRat
    linarith

/-- `ofNumber` returns zero only for a `Number` below `10⁻⁸¹` in magnitude. The 16 digit exponent is then
below `-96`. -/
lemma IOUAmount.ofNumber_underflow_truth_small_proof (sum : Number) (mode : rounding_mode) (result : IOUAmount)
    (h_lo : 10 ^ 18 ≤ sum.mantissa_.toNat) (h_hi : sum.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ sum.exponent_ + 3) (he_hi : sum.exponent_ + 4 ≤ maxExponent)
    (hok : IOUAmount.ofNumber sum mode = .ok result) (hres0 : result.mantissa_ = 0) :
    |sum.toRat| < (10 : ℚ) ^ (-81 : ℤ) := by
  unfold IOUAmount.ofNumber IOUAmount.fromNumber at hok
  cases hnorm : sum.normalizeToRange cMinValue cMaxValue mode with
  | error err => rw [hnorm] at hok; simp at hok
  | ok me =>
    obtain ⟨m, e⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hmant := normalizeToRange_16_mantissa_range sum mode m e h_lo h_hi he_lo he_hi hnorm
    have herange := normalizeToRange_16_exp_range sum mode m e h_lo h_hi he_lo he_hi hnorm
    by_cases hhi : e > cMaxOffset
    · rw [if_pos hhi] at hok; simp at hok
    rw [if_neg hhi] at hok
    by_cases hlo : e < cMinOffset
    · -- the 16 digit exponent is below `-96`, so the 19 digit exponent is at most `-100`
      have hE : sum.exponent_ ≤ -100 := by
        have h1 := herange.1
        rw [show cMinOffset = (-96 : ℤ) from rfl] at hlo
        omega
      have hM : (sum.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℤ) := by
        have : (sum.mantissa_.toNat : ℚ) < ((10 ^ 19 : ℕ) : ℚ) := by exact_mod_cast h_hi
        rwa [show ((10 ^ 19 : ℕ) : ℚ) = (10 : ℚ) ^ (19 : ℤ) by push_cast; norm_num] at this
      rw [_root_.XRPL.Model.Protocol.abs_toRat_eq sum]
      calc (sum.mantissa_.toNat : ℚ) * 10 ^ sum.exponent_
          < (10 : ℚ) ^ (19 : ℤ) * 10 ^ sum.exponent_ :=
            mul_lt_mul_of_pos_right hM (zpow_pos (by norm_num) _)
        _ ≤ (10 : ℚ) ^ (19 : ℤ) * 10 ^ (-100 : ℤ) :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hE) (by positivity)
        _ = (10 : ℚ) ^ (-81 : ℤ) := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
    · -- the clamp passed, so the result keeps its 16 digit mantissa
      exfalso
      rw [if_neg hlo] at hok
      have hres : result = ⟨m, e⟩ := (Except.ok.inj hok).symm
      have hm0 : m = 0 := by rw [hres] at hres0; exact hres0
      have h := hmant.1
      rw [hm0, show cMinValue.toNat = 10 ^ 15 from by decide] at h
      simp at h

/-- `normalize` returns zero for a 17 or 18 digit mantissa only when the exact value is below `10⁻⁸¹` in
magnitude. -/
lemma IOUAmount.normalize_underflow_truth_small_proof (m : Int64) (e : Int) (mode : rounding_mode)
    (result : IOUAmount)
    (hm_lo : 10 ^ 16 ≤ m.toInt.natAbs) (hm_hi : m.toInt.natAbs < 10 ^ 18)
    (he_hi : e + 4 ≤ maxExponent)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok result) (hres0 : result.mantissa_ = 0) :
    |(m.toInt : ℚ) * 10 ^ e| < (10 : ℚ) ^ (-81 : ℤ) := by
  have hpe : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  have hmabs : |(m.toInt : ℚ) * 10 ^ e| = (m.toInt.natAbs : ℚ) * 10 ^ e := by
    rw [abs_mul, abs_of_pos hpe, Nat.cast_natAbs]; push_cast; ring
  have hmlt : (m.toInt.natAbs : ℚ) < (10 : ℚ) ^ (18 : ℤ) := by
    have : (m.toInt.natAbs : ℚ) < ((10 ^ 18 : ℕ) : ℚ) := by exact_mod_cast hm_hi
    rwa [show ((10 ^ 18 : ℕ) : ℚ) = (10 : ℚ) ^ (18 : ℤ) by push_cast; norm_num] at this
  by_cases he : e < minExponent + 18
  · -- far below every IOU amount, whatever `normalize` returns
    rw [hmabs]
    calc (m.toInt.natAbs : ℚ) * 10 ^ e
        < (10 : ℚ) ^ (18 : ℤ) * 10 ^ e := mul_lt_mul_of_pos_right hmlt hpe
      _ ≤ (10 : ℚ) ^ (18 : ℤ) * 10 ^ (-99 : ℤ) :=
          mul_le_mul_of_nonneg_left
            (zpow_le_zpow_right₀ (by norm_num) (by have hm : minExponent = -32768 := rfl; omega))
            (by positivity)
      _ = (10 : ℚ) ^ (-81 : ℤ) := by
          rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
  · -- `from_rep` is exact, and the rest is `ofNumber` on its 19 digit result
    push Not at he
    have hne_min : m ≠ Int64.minValue := by
      intro h
      rw [h, show Int64.minValue.toInt.natAbs = 9223372036854775808 from by decide] at hm_hi
      omega
    obtain ⟨v, hfr, hv_val, hv_norm⟩ := Number.from_rep_exact m e mode hne_min he (by omega)
    have hm_ne : (⟨m, e⟩ : IOUAmount).mantissa_ ≠ 0 := by
      show m ≠ 0
      intro h; rw [h] at hm_lo; simp at hm_lo
    unfold IOUAmount.normalize at hok
    rw [if_neg (by simpa using hm_ne), hfr] at hok
    simp only at hok
    have hofn : IOUAmount.ofNumber v mode = .ok result := hok
    have hv_abs : |v.toRat| = (m.toInt.natAbs : ℚ) * 10 ^ e := by rw [hv_val, hmabs]
    have hm_pos : (0 : ℚ) < (m.toInt.natAbs : ℚ) := by
      have : 0 < m.toInt.natAbs := by omega
      exact_mod_cast this
    have hv_ne : v.mantissa_ ≠ 0 := by
      intro h0
      rw [Number.toRat_eq_zero_of_mantissa_zero v h0, abs_zero] at hv_abs
      have := mul_pos hm_pos hpe
      linarith
    have hv_mant := hv_norm.mantissaBounds_nat hv_ne
    have hv_exp_lo : minExponent ≤ v.exponent_ := by
      rcases hv_norm with hz | ⟨_, _, _, hlo, _⟩
      · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
      · exact hlo
    -- the 19 digit mantissa is larger than `|m|`, so the exponent went down
    have hv_exp_hi : v.exponent_ < e := by
      by_contra hc
      push Not at hc
      have h1 : (10 : ℚ) ^ e ≤ 10 ^ v.exponent_ := zpow_le_zpow_right₀ (by norm_num) hc
      have hvm18 : (10 : ℚ) ^ (18 : ℤ) ≤ (v.mantissa_.toNat : ℚ) := by
        have : ((10 ^ 18 : ℕ) : ℚ) ≤ (v.mantissa_.toNat : ℚ) := by exact_mod_cast hv_mant.1
        rwa [show ((10 ^ 18 : ℕ) : ℚ) = (10 : ℚ) ^ (18 : ℤ) by push_cast; norm_num] at this
      have habs := _root_.XRPL.Model.Protocol.abs_toRat_eq v
      rw [hv_abs] at habs
      have h2 : (10 : ℚ) ^ (18 : ℤ) * 10 ^ e ≤ (v.mantissa_.toNat : ℚ) * 10 ^ v.exponent_ :=
        mul_le_mul hvm18 h1 hpe.le (by positivity)
      have h3 : (m.toInt.natAbs : ℚ) * 10 ^ e < (10 : ℚ) ^ (18 : ℤ) * 10 ^ e :=
        mul_lt_mul_of_pos_right hmlt hpe
      linarith
    rw [← hv_val]
    exact IOUAmount.ofNumber_underflow_truth_small_proof v mode result hv_mant.1 hv_mant.2
      (by omega) (by omega) hofn hres0

/-- An IOU sum is zero only when the exact sum is below `10⁻⁸¹` in magnitude. A larger sum survives both the
19 digit add and the 16 digit re-round. -/
lemma IOUAmount.operator_add_underflow_truth_small_proof (x y result : IOUAmount) (mode : rounding_mode)
    (hx : x.InRange16) (hy : y.InRange16)
    (hok : IOUAmount.operator_add x y mode = .ok result) (hres0 : result.mantissa_ = 0) :
    |x.toRat + y.toRat| < (10 : ℚ) ^ (-81 : ℤ) := by
  by_contra hcon
  push Not at hcon
  have hm : minExponent = -32768 := rfl
  have hM : maxExponent = 32768 := rfl
  have hxm : x.mantissa_ ≠ 0 := by intro h; have := hx.mant_lo; rw [h] at this; simp at this
  have hym : y.mantissa_ ≠ 0 := by intro h; have := hy.mant_lo; rw [h] at this; simp at this
  obtain ⟨xn, hxn_eq, hxn_val, hxn_norm, hxn_ne⟩ := IOUAmount.toNumber_canonical x mode hx.mant_lo hx.mant_hi
    (by have := hx.exp_lo; omega) (by have := hx.exp_hi; omega)
  obtain ⟨yn, hyn_eq, hyn_val, hyn_norm, hyn_ne⟩ := IOUAmount.toNumber_canonical y mode hy.mant_lo hy.mant_hi
    (by have := hy.exp_lo; omega) (by have := hy.exp_hi; omega)
  unfold IOUAmount.operator_add at hok
  rw [if_neg (by simpa using hym), if_neg (by simpa using hxm), hxn_eq, hyn_eq] at hok
  simp only at hok
  cases hadd : Number.operator_add xn yn mode with
  | error e => rw [hadd] at hok; simp at hok
  | ok sum =>
    rw [hadd] at hok
    simp only at hok
    -- the 19 digit sum stays at or above `10⁻⁸¹`
    obtain ⟨h_no_cancel, hsum_ne, hsum_big⟩ := Number.operator_add_abs_ge_iou_min xn yn sum mode
      hxn_norm hyn_norm hxn_ne hyn_ne hadd (by rw [hxn_val, hyn_val]; exact hcon)
    have hsum_norm := operator_add_result_isNormalized_anyMode xn yn sum mode
      hxn_norm hyn_norm hxn_ne hyn_ne h_no_cancel hadd hsum_ne
    have hsum_mant := hsum_norm.mantissaBounds_nat hsum_ne
    have hsum_exp_lo : minExponent ≤ sum.exponent_ := by
      rcases hsum_norm with hz | ⟨_, _, _, hlo, _⟩
      · exact absurd (show sum.mantissa_ = 0 by rw [hz]; rfl) hsum_ne
      · exact hlo
    have he_hi : sum.exponent_ + 4 ≤ maxExponent :=
      IOUAmount.add_sum_exponent_hi_anyMode x y xn yn sum mode hxn_val hyn_val hxn_norm hyn_norm
        hxn_ne hyn_ne h_no_cancel hsum_ne hx.mant_hi hy.mant_hi
        (by have := hx.exp_hi; omega) (by have := hy.exp_hi; omega) hadd
    -- so the 16 digit re-round cannot return zero
    have hsmall := IOUAmount.ofNumber_underflow_truth_small_proof sum mode result
      hsum_mant.1 hsum_mant.2 (by omega) he_hi hok hres0
    linarith

end XRPL.Model.Protocol
