import XRPL.Properties.Vault.Proofs.Support.OfNumberFractional
import XRPL.Properties.Vault.Proofs.Support.NumberFacts
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangeBound
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Sum
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Proofs
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.Number.Add.Common.NormalizedSum
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.AtExponent

/-! # IOU conversions and roundings never fail within range

A positive value below the IOU ceiling converts to an IOU amount to nearest or down, two canonical IOU amounts add
while their sum stays in range, and a nonnegative IOU amount rounds to any scale in `[-96, 79]`. -/

namespace XRPL.Model.Protocol

/-- A to-nearest IOU `ofNumber` of a positive value below `(10^16 - 1/2)·10^80` never throws. The rounding
moves the value by at most half a unit of its 16th digit, so it never carries past the IOU ceiling. -/
lemma STAmount.ofNumber_fractional_ok_below (r : Number) (hn : r.isNormalized) (hpos : 0 < r.toRat)
    (hlt : r.toRat < (10 ^ 16 - 1 / 2) * 10 ^ 80) :
    ∃ result, STAmount.ofNumber .fractional r .to_nearest = .ok result := by
  have hr_ne : r.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hr_ne
  have hneg := Number.negative_false_of_pos r hpos
  have hre_lo := Number.exponent_ge_min r hn hr_ne
  have hre_hi : r.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt r 77 hn hneg (by unfold minExponent; norm_num) (by norm_num; linarith)
  by_cases h4 : r.exponent_ + 4 ≤ cMaxOffset
  · exact STAmount.ofNumber_fractional_ok r .to_nearest hr_lo hr_hi hre_lo h4
  have hco : cMaxOffset = 80 := rfl
  have hme : maxExponent = 32768 := rfl
  have he77 : r.exponent_ = 77 := by omega
  obtain ⟨⟨mant, exp⟩, hnorm⟩ := normalizeToRange_16_ok r .to_nearest hr_lo hr_hi (by omega) (by omega)
  obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, -⟩, hsgn⟩ :=
    normalizeToRange_iou_ok_facts r .to_nearest mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hhalf := normalizeToRange_16_within_half_ulp r mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hrange := normalizeToRange_16_exp_range r .to_nearest mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hneg
  have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
    have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
  have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
    rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
    exact this
  have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
    rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
    omega
  -- a carry would need a value of at least `10^96`, half a unit above the bound
  have hexp_hi : exp ≤ cMaxOffset := by
    by_contra hc
    have hexp : exp = 81 := by omega
    have hm15 : (10 : ℚ) ^ 15 ≤ (mant.toInt : ℚ) := by
      have h' : ((10 ^ 15 : ℕ) : ℤ) ≤ mant.toInt := by omega
      exact_mod_cast h'
    rw [hexp, he77] at hhalf
    have h1 := (abs_le.mp hhalf).2
    norm_num at h1
    nlinarith
  have hs : decide (r.signum < 0) = false := by
    simpa using Number.signum_nonneg_of_negative_false r hneg
  have hnorm' : r.normalizeToRange kMinValue kMaxValue .to_nearest = .ok (mant, exp) := hnorm
  unfold STAmount.ofNumber
  rw [if_neg (by decide), hs]
  simp only [Bool.false_eq_true, if_false, hnorm']
  have h_int : ¬ (STAmount.unchecked .fractional mant.toUInt64 exp false).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_fit : mant.toUInt64.toNat < 2 ^ 63 := by omega
  have h_sd : (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops.toInt64
      = if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant.toUInt64 exp false).mValue.toNat < 10 ^ 16 from hmtu_hi),
        signed_mantissa_toInt false mant.toUInt64 h_fit]
    show (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    simp
  have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp false).iou .to_nearest
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64, exp⟩) := by
    rw [STAmount.iou_of_lt .to_nearest h_int h_fit]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant.toUInt64 exp false .to_nearest hmtu_lo hmtu_hi
      (by omega) (by omega)
  rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa using hmant_pos)), ok_bind,
    STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_neg h_int, hiou, if_neg (by omega)]
  split_ifs <;> exact ⟨_, rfl⟩

/-- A downward IOU `ofNumber` of a positive value below `10^96` never throws. Rounding down never carries past
the IOU ceiling. -/
lemma STAmount.ofNumber_fractional_downward_ok (r : Number) (hn : r.isNormalized) (hpos : 0 < r.toRat)
    (hlt : r.toRat < 10 ^ 96) : ∃ result, STAmount.ofNumber .fractional r .downward = .ok result := by
  have hr_ne : r.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hpos.ne'
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hr_ne
  have hneg := Number.negative_false_of_pos r hpos
  have hre_lo := Number.exponent_ge_min r hn hr_ne
  have hre_hi : r.exponent_ ≤ 77 :=
    Number.exponent_le_of_toRat_lt r 77 hn hneg (by unfold minExponent; norm_num) (by norm_num; linarith)
  by_cases h4 : r.exponent_ + 4 ≤ cMaxOffset
  · exact STAmount.ofNumber_fractional_ok r .downward hr_lo hr_hi hre_lo h4
  have hco : cMaxOffset = 80 := rfl
  have hme : maxExponent = 32768 := rfl
  have he77 : r.exponent_ = 77 := by omega
  obtain ⟨⟨mant, exp⟩, hnorm⟩ := normalizeToRange_16_ok r .downward hr_lo hr_hi (by omega) (by omega)
  obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, -⟩, hsgn⟩ :=
    normalizeToRange_iou_ok_facts r .downward mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hdown := normalizeToRange_16_downward r mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hrange := normalizeToRange_16_exp_range r .downward mant exp hr_lo hr_hi (by omega) (by omega) hnorm
  have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hneg
  have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
    have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
  have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
    rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
    exact this
  have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
    rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
    omega
  -- a carry would need a value of at least `10^96`
  have hexp_hi : exp ≤ cMaxOffset := by
    by_contra hc
    have hexp : exp = 81 := by omega
    have hm15 : (10 : ℚ) ^ 15 ≤ (mant.toInt : ℚ) := by
      have h' : ((10 ^ 15 : ℕ) : ℤ) ≤ mant.toInt := by omega
      exact_mod_cast h'
    rw [hexp] at hdown
    have : (10 : ℚ) ^ 15 * 10 ^ (81 : ℤ) ≤ (mant.toInt : ℚ) * 10 ^ (81 : ℤ) :=
      mul_le_mul_of_nonneg_right hm15 (by positivity)
    norm_num at this
    linarith
  have hs : decide (r.signum < 0) = false := by
    simpa using Number.signum_nonneg_of_negative_false r hneg
  have hnorm' : r.normalizeToRange kMinValue kMaxValue .downward = .ok (mant, exp) := hnorm
  unfold STAmount.ofNumber
  rw [if_neg (by decide), hs]
  simp only [Bool.false_eq_true, if_false, hnorm']
  have h_int : ¬ (STAmount.unchecked .fractional mant.toUInt64 exp false).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_fit : mant.toUInt64.toNat < 2 ^ 63 := by omega
  have h_sd : (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops.toInt64
      = if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant.toUInt64 exp false).mValue.toNat < 10 ^ 16 from hmtu_hi),
        signed_mantissa_toInt false mant.toUInt64 h_fit]
    show (STAmount.unchecked .fractional mant.toUInt64 exp false).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    simp
  have hiou : (STAmount.unchecked .fractional mant.toUInt64 exp false).iou .downward
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if false then -mant.toUInt64.toInt64 else mant.toUInt64.toInt64, exp⟩) := by
    rw [STAmount.iou_of_lt .downward h_int h_fit]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant.toUInt64 exp false .downward hmtu_lo hmtu_hi
      (by omega) (by omega)
  rw [Int64.toUInt64Checked_of_nonneg (Int64.le_iff_toInt_le.mpr (by simpa using hmant_pos)), ok_bind,
    STAmount.checked]
  unfold STAmount.canonicalize
  rw [if_neg h_int, hiou, if_neg (by omega)]
  split_ifs <;> exact ⟨_, rfl⟩

/-- A `Number` converts to an IOU amount without error while its exponent is at most `76`. The 16-digit
rounding moves the exponent up by at most four, so it stays within the IOU range. -/
lemma STAmount.ofIOU_ofNumber_ok (n : Number) (mode : rounding_mode)
    (hn : n.mantissa_ ≠ 0 → n.isNormalized ∧ n.exponent_ ≤ 76) :
    ∃ r, (match IOUAmount.ofNumber n mode with
      | .error e => (Except.error e : Except Error STAmount)
      | .ok sumI => STAmount.ofIOUAmount sumI mode) = .ok r := by
  by_cases h0 : n.mantissa_ = 0
  · rw [IOUAmount.ofNumber_zero_mantissa n mode h0]
    exact ⟨_, STAmount.ofIOU_zero mode⟩
  obtain ⟨hnn, he⟩ := hn h0
  obtain ⟨hlo, hhi⟩ := hnn.mantissaBounds_nat h0
  have hemin := Number.exponent_ge_min n hnn h0
  have he_lo : minExponent ≤ n.exponent_ + 3 := by omega
  have he_hi : n.exponent_ + 4 ≤ maxExponent := by unfold maxExponent; omega
  obtain ⟨⟨m, e⟩, hnorm⟩ := normalizeToRange_16_ok n mode hlo hhi he_lo he_hi
  have herange := normalizeToRange_16_exp_range n mode m e hlo hhi he_lo he_hi hnorm
  have hof : IOUAmount.ofNumber n mode =
      if e < cMinOffset then .ok IOUAmount.zero else .ok ⟨m, e⟩ := by
    unfold IOUAmount.ofNumber IOUAmount.fromNumber
    rw [hnorm]
    simp only
    rw [if_neg (by unfold cMaxOffset; omega)]
  by_cases hmin : e < cMinOffset
  · rw [hof, if_pos hmin]
    exact ⟨_, STAmount.ofIOU_zero mode⟩
  · have hof' : IOUAmount.ofNumber n mode = .ok ⟨m, e⟩ := by rw [hof, if_neg hmin]
    rw [hof']
    have hmr := normalizeToRange_16_mantissa_range n mode m e hlo hhi he_lo he_hi hnorm
    have hcmin : cMinValue.toNat = 10 ^ 15 := by decide
    have hne : (⟨m, e⟩ : IOUAmount).mantissa_ ≠ 0 := by
      intro hz
      have : m.toInt.natAbs = 0 := by
        show (⟨m, e⟩ : IOUAmount).mantissa_.toInt.natAbs = 0
        rw [hz]; rfl
      omega
    have hr := IOUAmount.ofNumber_InRange16 n mode ⟨m, e⟩ hlo hhi he_lo he_hi hof' hne
    exact ⟨_, STAmount.ofIOU_canonical _ mode hr⟩

/-- Adding two canonical IOU amounts never throws while the 19-digit sum has an exponent at most `76`. -/
lemma STAmount.operator_add_iou_ok (v1 v2 : STAmount) (mode : rounding_mode) (hc1 : v1.IOUCanonical)
    (hc2 : v2.IOUCanonical)
    (hexp : ∀ n, Number.operator_add ⟨v1.mIsNegative, v1.mValue * 10 * 10 * 10, v1.mOffset - 3⟩
      ⟨v2.mIsNegative, v2.mValue * 10 * 10 * 10, v2.mOffset - 3⟩ mode = .ok n → n.mantissa_ ≠ 0 →
      n.exponent_ ≤ 76) :
    ∃ r, STAmount.operator_add v1 v2 mode = .ok r := by
  rw [STAmount.operator_add_iou_unfold v1 v2 mode hc1 hc2]
  have hn1 := lift_isNormalized v1.mIsNegative v1.mValue v1.mOffset hc1.mant_lo hc1.mant_hi
    (by have := hc1.exp_lo; unfold minExponent; omega) (by have := hc1.exp_hi; unfold maxExponent; omega)
  have hn2 := lift_isNormalized v2.mIsNegative v2.mValue v2.mOffset hc2.mant_lo hc2.mant_hi
    (by have := hc2.exp_lo; unfold minExponent; omega) (by have := hc2.exp_hi; unfold maxExponent; omega)
  obtain ⟨n, hadd⟩ := Number.operator_add_ok_of_exp _ _ mode hn1 hn2
    (by show v1.mOffset - 3 + 22 ≤ maxExponent; have := hc1.exp_hi; unfold maxExponent; omega)
    (by show v2.mOffset - 3 + 22 ≤ maxExponent; have := hc2.exp_hi; unfold maxExponent; omega)
  rw [hadd]
  exact STAmount.ofIOU_ofNumber_ok n mode
    (fun h0 => ⟨operator_add_isNormalized _ _ _ mode hn1 hn2 hadd h0, hexp n hadd h0⟩)

/-- A sum in any mode of a true value between zero and `5·10^18` units at exponent `t` has its exponent at
most `t`. -/
private lemma Number.add_exponent_le_any (x y n : Number) (t : Int) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hok : Number.operator_add x y mode = .ok n) (h0 : 0 ≤ x.toRat + y.toRat)
    (ht : minExponent + 18 ≤ t ∧ t ≤ maxExponent - 1) (hlt : x.toRat + y.toRat ≤ 5 * 10 ^ 18 * 10 ^ t) :
    n.exponent_ ≤ t := by
  have hn := Number.operator_add_isNormalized_any x y n mode hx hy hok
  by_cases hm0 : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn hm0]
    show (-2147483648 : Int) ≤ t
    have := ht.1; unfold minExponent at this; omega
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (5 * 10 ^ 18) t (by constructor <;> norm_num) ht
  have hwv' : w.toRat = 5 * 10 ^ 18 * 10 ^ t := by rw [hwv]; push_cast; ring
  have hlow : ∀ l, Number.lower (x.toRat + y.toRat) = some l → 0 ≤ l.toRat ∧ l.toRat ≤ w.toRat := by
    intro l hl
    refine ⟨?_, le_trans (Number.lower_le _ l hl) (by rw [hwv']; exact hlt)⟩
    have := Number.lower_tight _ l hl Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact h0)
    rwa [Number.toRat_zero] at this
  have hup : ∀ u, Number.upper (x.toRat + y.toRat) = some u → 0 ≤ u.toRat ∧ u.toRat ≤ w.toRat := fun u hu =>
    ⟨le_trans h0 (Number.le_upper _ u hu), Number.upper_tight _ u hu w hw (by rw [hwv']; exact hlt)⟩
  have hb : 0 ≤ n.toRat ∧ n.toRat ≤ w.toRat := by
    cases mode with
    | to_nearest =>
      rcases operator_add_rounded_to_nearest x y n hx hy hok with ⟨l, hl, hv⟩ | ⟨u, hu, hv⟩
      · rw [hv]; exact hlow l hl
      · rw [hv]; exact hup u hu
    | upward =>
      obtain ⟨u, hu, hv⟩ := operator_add_rounded_upward x y n hx hy hok hm0
      rw [hv]; exact hup u hu
    | downward =>
      obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward x y n hx hy hok hm0
      rw [hv]; exact hlow l hl
    | towards_zero =>
      obtain ⟨m, hm, hv⟩ := operator_add_rounded_towards_zero x y n hx hy hok
      rw [if_pos h0] at hm
      rw [hv]; exact hlow m hm
  have hp : (0 : ℚ) < 10 ^ t := zpow_pos (by norm_num) _
  exact Number.exponent_le_of_toRat_lt n t hn (Number.negative_false_of_nonneg n hn hb.1) ht.1
    (by rw [hwv'] at hb; nlinarith [hb.2])

/-- Rounding a nonnegative IOU amount to a scale never throws, in every mode, for a scale in `[-96, 79]`. -/
lemma STAmount.roundToExponent_ok_any (value : STAmount) (s : Int) (mode : rounding_mode) (hc : value.IOUCanonical)
    (hneg : value.mIsNegative = false) (hs_lo : -96 ≤ s) (hs_hi : s ≤ 79) :
    ∃ r, STAmount.roundToExponent value s mode = .ok r := by
  have h_int : value.integral = false := by unfold STAmount.integral; rw [hc.is_fractional]; rfl
  by_cases hexp : s ≤ value.exponent
  · exact ⟨value, STAmount.roundToExponent_eq_self value s _ (Or.inr (Or.inr hexp))⟩
  push Not at hexp
  have h_ev : value.mOffset < s := hexp
  have h_mv : value.mValue ≠ 0 := by
    intro h0
    have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo
    omega
  have hz : value.isZero = false := by simp [STAmount.isZero, h_mv]
  have hkMin : kMinValue.toNat = 10 ^ 15 := by decide
  have hps : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have h1000 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (s - 3) = 10 ^ 15 * 10 ^ s := by
    rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; field_simp
  have hts : minExponent + 18 ≤ s - 3 ∧ s - 3 ≤ maxExponent - 1 := by unfold minExponent maxExponent; omega
  unfold STAmount.roundToExponent
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg (by rw [hz]; exact Bool.false_ne_true),
    if_neg (not_le.mpr hexp)]
  have hchk : STAmount.checked value.mNumericType kMinValue s value.negative mode =
      .ok ⟨.fractional, kMinValue, s, false⟩ := by
    rw [hc.is_fractional]
    show STAmount.checked .fractional kMinValue s value.mIsNegative mode = _
    rw [hneg]
    exact STAmount.checked_reference s false mode hs_lo (by omega)
  rw [hchk]
  simp only []
  set refA : STAmount := ⟨.fractional, kMinValue, s, false⟩ with hrefA_def
  have hcr : refA.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ s; omega, by show s ≤ 80; omega⟩
  have hrefv : refA.toRat = (10 : ℚ) ^ 15 * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg refA rfl]
    show (kMinValue.toNat : ℚ) * 10 ^ s = _
    rw [hkMin]; push_cast; ring
  have hvv : value.toRat < (10 : ℚ) ^ 15 * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg value hneg]
    have hm : (value.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc.mant_hi
    have hp : (10 : ℚ) ^ value.mOffset ≤ (10 : ℚ) ^ (s - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h10 : (10 : ℚ) ^ (s - 1) * 10 = (10 : ℚ) ^ s := by
      rw [← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; congr 1; ring
    calc (value.mValue.toNat : ℚ) * 10 ^ value.mOffset
        ≤ (value.mValue.toNat : ℚ) * 10 ^ (s - 1) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ < 10 ^ 16 * 10 ^ (s - 1) := mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
      _ = 10 ^ 15 * 10 ^ s := by rw [← h10]; ring
  have hv0 : 0 ≤ value.toRat := by rw [STAmount.toRat_of_nonneg value hneg]; positivity
  have hb5 : (10 : ℚ) ^ 15 * 10 ^ s * 2 ≤ 5 * 10 ^ 18 * 10 ^ (s - 3) := by
    rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; field_simp; norm_num
  obtain ⟨sum, hsum⟩ : ∃ sum, STAmount.operator_add value refA mode = .ok sum := by
    apply STAmount.operator_add_iou_ok value refA mode hc hcr
    intro n hadd hn0
    have := Number.add_exponent_le_any _ _ n (s - 3) mode
      (lift_isNormalized _ _ _ hc.mant_lo hc.mant_hi (by have := hc.exp_lo; unfold minExponent; omega)
        (by have := hc.exp_hi; unfold maxExponent; omega))
      (lift_isNormalized _ _ _ hcr.mant_lo hcr.mant_hi (by show minExponent ≤ s - 3; unfold minExponent; omega)
        (by show s - 3 ≤ maxExponent; unfold maxExponent; omega))
      hadd (by rw [lift_toRat value hc.mant_hi, lift_toRat refA hcr.mant_hi, hrefv]; positivity) hts
      (by rw [lift_toRat value hc.mant_hi, lift_toRat refA hcr.mant_hi, hrefv]; linarith)
    omega
  rw [hsum]
  simp only []
  have hrefeq : refA = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
    rw [hc.is_fractional, hneg]
  obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, -⟩ :=
    STAmount.roundToExponent_sum_spec value s mode hc h_ev hs_lo (by omega) sum (by rw [← hrefeq]; exact hsum)
  have hc_sum : sum.IOUCanonical :=
    { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
      mant_lo := by omega
      mant_hi := by omega
      exp_lo := by rw [h_sum_off]; omega
      exp_hi := by rw [h_sum_off]; omega }
  have hsumv : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg sum (by rw [h_sum_neg, hneg]), h_sum_mv, h_sum_off]
  unfold STAmount.operator_sub
  have h_negRef : refA.operator_neg = ⟨.fractional, kMinValue, s, true⟩ := by
    rw [STAmount.operator_neg_of_ne refA (by show kMinValue ≠ 0; decide)]
    rfl
  rw [h_negRef]
  set negRef : STAmount := ⟨.fractional, kMinValue, s, true⟩ with hnegRef_def
  have hcneg : negRef.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ s; omega, by show s ≤ 80; omega⟩
  have hnegv : negRef.toRat = -((10 : ℚ) ^ 15 * 10 ^ s) := by
    rw [STAmount.toRat_of_neg negRef rfl]
    show -((kMinValue.toNat : ℚ) * 10 ^ s) = _
    rw [hkMin]; push_cast; ring
  apply STAmount.operator_add_iou_ok sum negRef mode hc_sum hcneg
  intro n hadd hn0
  have hk : (k : ℚ) ≤ 10 ^ 15 := by exact_mod_cast hk_le
  have := Number.add_exponent_le_any _ _ n (s - 3) mode
    (lift_isNormalized _ _ _ hc_sum.mant_lo hc_sum.mant_hi
      (by have := hc_sum.exp_lo; unfold minExponent; omega) (by have := hc_sum.exp_hi; unfold maxExponent; omega))
    (lift_isNormalized _ _ _ hcneg.mant_lo hcneg.mant_hi (by show minExponent ≤ s - 3; unfold minExponent; omega)
      (by show s - 3 ≤ maxExponent; unfold maxExponent; omega))
    hadd
    (by rw [lift_toRat sum hc_sum.mant_hi, lift_toRat negRef hcneg.mant_hi, hsumv, hnegv]; push_cast; nlinarith)
    hts
    (by rw [lift_toRat sum hc_sum.mant_hi, lift_toRat negRef hcneg.mant_hi, hsumv, hnegv]; push_cast; nlinarith)
  omega

end XRPL.Model.Protocol
