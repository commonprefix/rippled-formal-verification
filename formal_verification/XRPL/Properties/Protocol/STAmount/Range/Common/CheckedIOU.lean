import XRPL.Properties.Protocol.STAmount.Range.Common.IOU16
import XRPL.Properties.Protocol.STAmount.Range.Common.Checked
import XRPL.Properties.Protocol.Number.Constructors.Constructors
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Normalize.RoundsWithin
import XRPL.Properties.Protocol.Number.Normalize.NormalizedResult
import XRPL.Properties.Protocol.Number.Totality

/-! # When `STAmount.checked` returns an IOU amount

For IOU, `checked` turns the mantissa and exponent into a 19-digit Number, which is exact for a mantissa within
int64, and then rounds it to 16 digits. It fails when the exponent of the result is above 80. -/

namespace XRPL.Model.Protocol

/-- A rounding within relative error `1/2` keeps at least half of the size. -/
lemma RoundsWithin_abs_ge_half {A : Type} [RatValued A] (result : A) (truth ε : ℚ) (mode : rounding_mode)
    (h : RoundsWithin result truth mode ε) (hε : ε ≤ 1 / 2) : |truth| ≤ |RatValued.toRat result| * 2 := by
  set r := RatValued.toRat result with hr
  have habs_nn : 0 ≤ |truth| := abs_nonneg _
  have hmul : |truth| * ε ≤ |truth| * (1 / 2) := mul_le_mul_of_nonneg_left hε habs_nn
  have htri := abs_sub_abs_le_abs_sub truth r
  unfold RoundsWithin at h
  cases mode with
  | to_nearest =>
    rw [abs_sub_comm] at h
    linarith
  | downward =>
    obtain ⟨hd, hm⟩ := h
    have h1 : |truth - r| ≤ |truth| * ε := by rw [abs_of_nonneg (by linarith)]; exact hm
    linarith
  | upward =>
    obtain ⟨hd, hm⟩ := h
    have h1 : |truth - r| ≤ |truth| * ε := by rw [abs_of_nonpos (by linarith), neg_sub]; exact hm
    linarith
  | towards_zero =>
    obtain ⟨-, hm⟩ := h
    linarith

/-- A nonzero `from_rep` result is within a factor of two of `mantissa * 10 ^ exponent` in size, in every mode. -/
lemma Number.from_rep_abs_bounds (mantissa : Int64) (e : Int) (mode : rounding_mode) (result : Number)
    (hok : Number.from_rep mantissa e largeRange.min largeRange.max mode = .ok result)
    (hr : result.mantissa_ ≠ 0) :
    |result.toRat| ≤ |(mantissa.toInt : ℚ) * 10 ^ e| * 2 ∧
      |(mantissa.toInt : ℚ) * 10 ^ e| ≤ |result.toRat| * 2 := by
  have hε1 : (5 / (2 ^ 63 + 7 : ℚ)) ≤ 1 / 2 := by norm_num
  have hε2 : (10 / (2 ^ 63 + 2 : ℚ)) ≤ 1 / 2 := by norm_num
  cases mode with
  | to_nearest =>
    have h := Number.from_rep_rounds_to_nearest mantissa e result hok hr
    exact ⟨RoundsWithin_abs_le_two result _ _ _ h (by linarith), RoundsWithin_abs_ge_half result _ _ _ h hε1⟩
  | towards_zero =>
    have h := Number.from_rep_rounds_towards_zero mantissa e result hok hr
    exact ⟨RoundsWithin_abs_le_two result _ _ _ h (by linarith), RoundsWithin_abs_ge_half result _ _ _ h hε2⟩
  | downward =>
    have h := Number.from_rep_rounds_downward mantissa e result hok hr
    exact ⟨RoundsWithin_abs_le_two result _ _ _ h (by linarith), RoundsWithin_abs_ge_half result _ _ _ h hε2⟩
  | upward =>
    have h := Number.from_rep_rounds_upward mantissa e result hok hr
    exact ⟨RoundsWithin_abs_le_two result _ _ _ h (by linarith), RoundsWithin_abs_ge_half result _ _ _ h hε2⟩

/-- Normalizing to 19 digits returns a result when the exponent is at least two below the largest one. -/
lemma doNormalize_largeRange_ok_of_exp (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode)
    (hm : m.toNat < 10 ^ 19) (he : e + 2 ≤ maxExponent) :
    ∃ r, doNormalize neg m e largeRange.min largeRange.max mode = .ok r := by
  rw [doNormalize_eq_spec]
  all_goals try min_fit
  unfold doNormalizeSpec
  by_cases hz : (m == 0) = true
  · rw [ite_eq_left hz]
    exact ⟨_, rfl⟩
  rw [ite_eq_right hz]
  rcases hsu : doNormalize_scaleUpSpec largeRange.min m e with ⟨m1, e1⟩
  have he1 : e1 ≤ e := by
    have := doNormalize_scaleUp_exp_le largeRange.min m e
    rwa [hsu] at this
  have hm1 : m1.toNat < 10 ^ 19 := by
    have := doNormalize_scaleUp_lt19 largeRange.min m e (by decide) hm
    rwa [hsu] at this
  simp only []
  rw [doNormalize_scaleDown_id _ m1 e1 _ (by rw [UInt64.le_iff_toNat_le, largeRange_max_val]; omega)]
  simp only []
  by_cases hund : (decide (e1 < minExponent) || decide (m1 < largeRange.min)) = true
  · rw [ite_eq_left hund]
    exact ⟨_, rfl⟩
  rw [ite_eq_right hund]
  obtain ⟨m', e', g', hcap, he'⟩ := doNormalize_capAtMaxRep_ok_of_exp m1 e1
    (if neg then Guard.new.set_negative else Guard.new) (by omega)
  rw [hcap]
  simp only []
  obtain ⟨res, hres⟩ := Guard.doRoundUp_ok_of_exp_le g' neg m' e' largeRange.min largeRange.max mode
    .normalize2 (by decide) (by omega)
  rw [hres]
  exact ⟨_, rfl⟩

/-- For a nonzero mantissa, `IOUAmount.normalize` makes the 19-digit Number and rounds it with
`IOUAmount.ofNumber`. -/
lemma IOUAmount.normalize_eq_ofNumber (a : IOUAmount) (mode : rounding_mode) (h : ¬ (a.mantissa_ == 0) = true) :
    IOUAmount.normalize a mode =
      match Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
      | .error err => .error err
      | .ok v => IOUAmount.ofNumber v mode := by
  unfold IOUAmount.normalize IOUAmount.ofNumber
  rw [ite_eq_right h]
  rfl

/-- An IOU `checked` returns a result exactly when the 19-digit Number of the signed mantissa exists and its
16-digit rounding does. -/
lemma STAmount.checked_fractional_ok_iff_from_rep (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hm : m.toNat < 2 ^ 63) (hm0 : m ≠ 0) :
    (∃ result, STAmount.checked .fractional m e neg mode = .ok result) ↔
      ∃ v, Number.from_rep (if neg then -m.toInt64 else m.toInt64) e largeRange.min largeRange.max mode = .ok v ∧
        ∃ r, IOUAmount.ofNumber v mode = .ok r := by
  have h_int : ¬ (STAmount.unchecked .fractional m e neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have hm_pos : 0 < m.toNat := by
    rcases Nat.eq_zero_or_pos m.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) hm0
    · exact h
  have h_sd : (STAmount.unchecked .fractional m e neg).signedDrops.toInt64
      = if neg then -m.toInt64 else m.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt_of_lt _
          (show (STAmount.unchecked .fractional m e neg).mValue.toNat < 2 ^ 63 from hm),
        signed_mantissa_toInt neg m hm]
    show (STAmount.unchecked .fractional m e neg).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    rcases neg <;> simp
  have hsd_ne : ¬ ((if neg then -m.toInt64 else m.toInt64) == 0) = true := by
    rw [beq_iff_eq]
    intro h
    have h' := congrArg Int64.toInt h
    rw [signed_mantissa_toInt neg m hm, show (0 : Int64).toInt = 0 from by decide] at h'
    rcases mul_eq_zero.mp h' with h1 | h1
    · cases neg <;> simp at h1
    · omega
  rw [STAmount.checked]
  unfold STAmount.canonicalize
  rw [ite_eq_right h_int, STAmount.iou_eq mode h_int hm, h_sd]
  unfold IOUAmount.ofMantissaExp
  rw [IOUAmount.normalize_eq_ofNumber _ mode hsd_ne]
  dsimp only [STAmount.unchecked]
  cases hfr : Number.from_rep (if neg then -m.toInt64 else m.toInt64) e largeRange.min largeRange.max mode with
  | error err => exact iff_of_false (by simp) (by simp)
  | ok v =>
    dsimp only
    cases hof : IOUAmount.ofNumber v mode with
    | error err =>
      refine iff_of_false (by simp) ?_
      rintro ⟨v', hv', r, hr⟩
      rw [← Except.ok.inj hv', hof] at hr
      exact absurd hr (by simp)
    | ok r => exact iff_of_true ⟨_, rfl⟩ ⟨v, rfl, r, hof⟩

/-- An IOU `checked` returns a result exactly when `mantissa * 10 ^ exponent` rounds into the IOU range. -/
lemma STAmount.checked_ok_iff_fractional (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hm : m.toNat ≤ 9223372036854775807) :
    (∃ result, STAmount.checked .fractional m e neg mode = .ok result) ↔
      STAmount.RoundsInRange .fractional mode (STAmount.unchecked .fractional m e neg).toRat := by
  have hu80 : (0 : ℚ) < (10 : ℚ) ^ (80 : ℤ) := zpow_pos (by norm_num) _
  have hlt : m.toNat < 2 ^ 63 := by omega
  by_cases hm0 : m = 0
  · -- a zero mantissa gives the zero amount
    subst hm0
    have hok : STAmount.checked .fractional 0 e neg mode = .ok ⟨.fractional, 0, -100, false⟩ := by
      have hsd : (STAmount.unchecked .fractional 0 e neg).signedDrops.toInt64 = 0 := by cases neg <;> rfl
      rw [STAmount.checked]
      unfold STAmount.canonicalize
      rw [ite_eq_right (by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]),
        STAmount.iou_eq mode (by simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral])
          (show (0 : UInt64).toNat < 2 ^ 63 by decide), hsd]
      rfl
    rw [hok, STAmount.unchecked_toRat, STAmount.roundsInRange_fractional_iff]
    exact iff_of_true ⟨_, rfl⟩ (roundsWithinUnits_of_abs_le mode _ _ _ hu80 (by simp))
  set sd : Int64 := if neg then -m.toInt64 else m.toInt64 with hsd
  have hsd_int : sd.toInt = (if neg then -1 else 1) * (m.toNat : ℤ) := signed_mantissa_toInt neg m hlt
  have hsd_ne_min : sd ≠ Int64.minValue := by
    intro h
    have h' := congrArg Int64.toInt h
    rw [hsd_int, show Int64.minValue.toInt = -9223372036854775808 from by decide] at h'
    cases neg
    · simp only [Bool.false_eq_true, ite_false, one_mul] at h'
      omega
    · simp only [ite_true, neg_one_mul] at h'
      omega
  -- the exact value, as the signed mantissa times the power of ten
  have hval : (STAmount.unchecked .fractional m e neg).toRat = (sd.toInt : ℚ) * 10 ^ e := by
    rw [STAmount.unchecked_toRat, hsd_int]
    cases neg <;> simp
  have hm_pos : 0 < m.toNat := by
    rcases Nat.eq_zero_or_pos m.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by rw [h]; rfl)) hm0
    · exact h
  have hmag_nat : sd.magnitude.toNat = m.toNat := by
    rw [Int64.toNat_magnitude, hsd_int]
    cases neg <;> simp
  have hm1 : (1 : ℚ) ≤ (m.toNat : ℚ) := by exact_mod_cast hm_pos
  have hm19 : (m.toNat : ℚ) < (10 : ℚ) ^ 19 := by
    have : m.toNat < 10 ^ 19 := by omega
    exact_mod_cast this
  have habs : |(sd.toInt : ℚ) * 10 ^ e| = (m.toNat : ℚ) * 10 ^ e := by
    rw [hsd_int, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℚ) < 10) e)]
    cases neg <;> simp
  have hpe : (0 : ℚ) < (10 : ℚ) ^ e := zpow_pos (by norm_num) _
  rw [STAmount.checked_fractional_ok_iff_from_rep m e neg mode hlt hm0, hval]
  have hminE : minExponent = -32768 := rfl
  have hmaxE : maxExponent = 32768 := rfl
  by_cases hlow : e < minExponent + 18
  · -- far below the IOU range: the result is zero or tiny, and so is the value
    obtain ⟨v, hv⟩ : ∃ v, Number.from_rep sd e largeRange.min largeRange.max mode = .ok v :=
      doNormalize_largeRange_ok_of_exp (decide (sd < 0)) sd.magnitude e mode (by rw [hmag_nat]; omega) (by omega)
    have hvn := Number.from_rep_isNormalized sd e mode v hv
    have hpow : (10 : ℚ) ^ e ≤ (10 : ℚ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_zero] at hpow
    have hsmall : |(sd.toInt : ℚ) * 10 ^ e| ≤ (10 : ℚ) ^ 19 := by
      rw [habs]
      nlinarith
    have hL : (2 : ℚ) * (10 : ℚ) ^ 19 ≤ ((9999999999999999 : ℕ) : ℚ) * (10 : ℚ) ^ (80 : ℤ) := by norm_num
    have hvsmall : |v.toRat| ≤ ((9999999999999999 : ℕ) : ℚ) * (10 : ℚ) ^ (80 : ℤ) := by
      by_cases hv0 : v.mantissa_ = 0
      · rw [Number.toRat_eq_zero_of_mantissa_zero v hv0, abs_zero]
        positivity
      · have := (Number.from_rep_abs_bounds sd e mode v hv hv0).1
        linarith
    rw [STAmount.roundsInRange_fractional_iff]
    refine iff_of_true ⟨v, hv, ?_⟩ (roundsWithinUnits_of_abs_le mode _ _ _ hu80 (by linarith))
    rw [IOUAmount.ofNumber_ok_iff v mode hvn, STAmount.roundsInRange_fractional_iff]
    exact roundsWithinUnits_of_abs_le mode _ _ _ hu80 hvsmall
  by_cases hhigh : maxExponent - 1 < e
  · -- far above the IOU range: both sides fail
    have hpow : (10 : ℚ) ^ (97 : ℤ) ≤ (10 : ℚ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hbig : (10 : ℚ) ^ (97 : ℤ) ≤ |(sd.toInt : ℚ) * 10 ^ e| := by
      rw [habs]
      nlinarith
    have hN : (((9999999999999999 : ℕ) : ℚ) + 1) * (10 : ℚ) ^ (80 : ℤ) * 2 < (10 : ℚ) ^ (97 : ℤ) := by
      norm_num
    rw [STAmount.roundsInRange_fractional_iff]
    refine iff_of_false ?_ (not_roundsWithinUnits_of_le_abs mode _ _ _ hu80 (by linarith))
    rintro ⟨v, hv, hr⟩
    have hvn := Number.from_rep_isNormalized sd e mode v hv
    rw [IOUAmount.ofNumber_ok_iff v mode hvn, STAmount.roundsInRange_fractional_iff] at hr
    have hvlt : |v.toRat| < (((9999999999999999 : ℕ) : ℚ) + 1) * (10 : ℚ) ^ (80 : ℤ) := by
      by_contra hc
      exact not_roundsWithinUnits_of_le_abs mode _ _ _ hu80 (not_lt.mp hc) hr
    by_cases hv0 : v.mantissa_ = 0
    · -- a zero result would mean a tiny value
      have hsmall := Number.normalize_underflow_truth_small
        (Number.unchecked (decide (sd < 0)) sd.magnitude e) v mode
        (by
          show sd.magnitude ≠ 0
          intro h
          have := congrArg UInt64.toNat h
          rw [hmag_nat] at this
          simp at this
          omega)
        hv hv0
      rw [abs_toRat_eq] at hsmall
      have hsmall' : (m.toNat : ℚ) * 10 ^ e < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
        have h : ((Number.unchecked (decide (sd < 0)) sd.magnitude e).mantissa_.toNat : ℚ) = (m.toNat : ℚ) := by
          show ((sd.magnitude.toNat : ℕ) : ℚ) = _
          rw [hmag_nat]
        rw [h] at hsmall
        exact hsmall
      have hmin18 : (10 : ℚ) ^ (minExponent : ℤ) ≤ (10 : ℚ) ^ (-18 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h18 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (-18 : ℤ) = 1 := by norm_num
      have h97 : (1 : ℚ) ≤ (10 : ℚ) ^ (97 : ℤ) := by norm_num
      rw [habs] at hbig
      nlinarith
    · have := (Number.from_rep_abs_bounds sd e mode v hv hv0).2
      linarith
  · -- the 19-digit Number is exact, so only the 16-digit rounding is left
    obtain ⟨v, hv, hvval, hvn⟩ := Number.from_rep_exact sd e mode hsd_ne_min (by omega) (by omega)
    rw [← hvval, ← IOUAmount.ofNumber_ok_iff v mode hvn]
    constructor
    · rintro ⟨v', hv', hr⟩
      rw [hv, Except.ok.injEq] at hv'
      rw [hv']
      exact hr
    · intro hr
      exact ⟨v, hv, hr⟩

/-- Proof of `STAmount.checked_ok_iff`. -/
lemma STAmount.checked_ok_iff_proof (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool) (mode : rounding_mode)
    (hnt : nt = .fractional ∨ nt = NumericType.native ∨ nt = NumericType.int64)
    (hm : m.toNat ≤ 9223372036854775807) :
    (∃ result, STAmount.checked nt m e neg mode = .ok result) ↔
      STAmount.RoundsInRange nt mode (STAmount.unchecked nt m e neg).toRat := by
  rcases hnt with rfl | rfl | rfl
  · exact STAmount.checked_ok_iff_fractional m e neg mode hm
  · exact STAmount.checked_ok_iff_native m e neg mode hm
  · exact STAmount.checked_ok_iff_int64 m e neg mode hm

end XRPL.Model.Protocol
