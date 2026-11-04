import XRPL.Properties.Lending.Loan.Common.RoundTotal
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.Number.ToRep.ToRep

/-! # Rounding to an asset never fails, for amounts of either sign

A number below `10^90` in size, of either sign, rounds to an IOU amount at any scale in `[-96, 79]`, and one a unit
below the XRP or MPT maximum rounds to that asset. The result is at most twice the size plus one unit. -/

namespace XRPL.Model.Protocol

open private STAmount.ofNumber_integral_reduce from XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality

/-- A sum in any mode is no bigger in size than a normalized bound on the true sum's size. -/
private lemma Number.add_abs_le_any (x y n w : Number) (mode : rounding_mode) (hx : x.isNormalized)
    (hy : y.isNormalized) (hok : Number.operator_add x y mode = .ok n) (hw : w.isNormalized)
    (hle : |x.toRat + y.toRat| ≤ w.toRat) : |n.toRat| ≤ w.toRat := by
  have hw' := Number.operator_neg_isNormalized w hw
  have hwv : w.operator_neg.toRat = -w.toRat := Number.toRat_neg w
  obtain ⟨h1, h2⟩ := abs_le.mp hle
  have hlow : ∀ l, Number.lower (x.toRat + y.toRat) = some l → |l.toRat| ≤ w.toRat := by
    intro l hl
    rw [abs_le]
    constructor
    · have := Number.lower_tight _ l hl _ hw' (by rw [hwv]; linarith)
      rw [hwv] at this
      linarith
    · linarith [Number.lower_le _ l hl]
  have hup : ∀ u, Number.upper (x.toRat + y.toRat) = some u → |u.toRat| ≤ w.toRat := by
    intro u hu
    rw [abs_le]
    exact ⟨by linarith [Number.le_upper _ u hu], Number.upper_tight _ u hu w hw h2⟩
  by_cases hm0 : n.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero n hm0, abs_zero]
    linarith [abs_nonneg (x.toRat + y.toRat)]
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
    rw [hv]
    split_ifs at hm
    · exact hlow m hm
    · exact hup m hm

/-- A sum of IOU amounts no bigger than `5·10^94` in size has its 19-digit sum's exponent at most `76`. -/
private lemma STAmount.lift_add_exponent_le (v1 v2 : STAmount) (mode : rounding_mode) (hc1 : v1.IOUCanonical)
    (hc2 : v2.IOUCanonical) (hle : |v1.toRat + v2.toRat| ≤ 5 * 10 ^ 94) :
    ∀ n, Number.operator_add ⟨v1.mIsNegative, v1.mValue * 10 * 10 * 10, v1.mOffset - 3⟩
      ⟨v2.mIsNegative, v2.mValue * 10 * 10 * 10, v2.mOffset - 3⟩ mode = .ok n → n.mantissa_ ≠ 0 →
      n.exponent_ ≤ 76 := by
  intro n hadd hn0
  have hn1 := lift_isNormalized v1.mIsNegative v1.mValue v1.mOffset hc1.mant_lo hc1.mant_hi
    (by have := hc1.exp_lo; unfold minExponent; omega) (by have := hc1.exp_hi; unfold maxExponent; omega)
  have hn2 := lift_isNormalized v2.mIsNegative v2.mValue v2.mOffset hc2.mant_lo hc2.mant_hi
    (by have := hc2.exp_lo; unfold minExponent; omega) (by have := hc2.exp_hi; unfold maxExponent; omega)
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (5 * 10 ^ 18) 76 (by constructor <;> norm_num)
    ⟨by unfold minExponent; norm_num, by unfold maxExponent; norm_num⟩
  have hb := Number.add_abs_le_any _ _ n w mode hn1 hn2 hadd hw (by
    rw [lift_toRat v1 hc1.mant_hi, lift_toRat v2 hc2.mant_hi, hwv]
    push_cast
    linarith [show (5 : ℚ) * 10 ^ 94 = 5 * 10 ^ 18 * 10 ^ (76 : ℤ) by norm_num])
  have hnn := operator_add_isNormalized _ _ _ mode hn1 hn2 hadd hn0
  have := Number.exponent_lt_of_abs_lt n hnn hn0 77 (by
    rw [hwv] at hb
    push_cast at hb
    have : (5 : ℚ) * 10 ^ 18 * 10 ^ (76 : ℤ) < 10 ^ ((77 : ℤ) + 18) := by norm_num
    linarith)
  omega

/-- An IOU amount below `10^16` units at an exponent below `s` is below `10^15` units at `s` in size. -/
private lemma STAmount.abs_lt_of_exponent_lt (v : STAmount) (s : Int) (hc : v.IOUCanonical) (h : v.mOffset < s) :
    |v.toRat| < 10 ^ 15 * 10 ^ s := by
  rw [STAmount.abs_toRat]
  have hm : (v.mValue.toNat : ℚ) < 10 ^ 16 := by exact_mod_cast hc.mant_hi
  have hp : (10 : ℚ) ^ v.mOffset ≤ (10 : ℚ) ^ (s - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h10 : (10 : ℚ) ^ (s - 1) * 10 = (10 : ℚ) ^ s := by
    rw [← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]; congr 1; ring
  calc (v.mValue.toNat : ℚ) * 10 ^ v.mOffset
      ≤ (v.mValue.toNat : ℚ) * 10 ^ (s - 1) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ < 10 ^ 16 * 10 ^ (s - 1) := mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
    _ = 10 ^ 15 * 10 ^ s := by rw [← h10]; ring

/-- A rounding of a nonzero sum stays within twice the sum's size, in every mode. -/
private lemma RoundsWithin.abs_le_two {r : STAmount} {t : ℚ} {mode : rounding_mode} {e : ℚ} (he : e ≤ 1)
    (h : RoundsWithin r t mode e) : |r.toRat| ≤ 2 * |t| := by
  have ht := abs_nonneg t
  have hte : |t| * e ≤ |t| := by nlinarith
  unfold RoundsWithin at h
  cases mode with
  | to_nearest =>
    have h' : |r.toRat - t| ≤ |t| * e := h
    have := abs_sub_abs_le_abs_sub r.toRat t
    linarith
  | upward =>
    obtain ⟨h1, h2⟩ : t ≤ r.toRat ∧ r.toRat - t ≤ |t| * e := h
    rw [abs_le]; constructor <;> linarith [neg_abs_le t, le_abs_self t]
  | downward =>
    obtain ⟨h1, h2⟩ : r.toRat ≤ t ∧ t - r.toRat ≤ |t| * e := h
    rw [abs_le]; constructor <;> linarith [neg_abs_le t, le_abs_self t]
  | towards_zero =>
    obtain ⟨h1, -⟩ : |r.toRat| ≤ |t| ∧ |t| - |r.toRat| ≤ |t| * e := h
    linarith

/-- Rounding a canonical IOU amount of either sign to a scale never throws, in every mode, for a scale in
`[-96, 79]`. -/
private lemma STAmount.roundToExponent_ok_abs (value : STAmount) (s : Int) (mode : rounding_mode)
    (hc : value.IOUCanonical) (hs_lo : -96 ≤ s) (hs_hi : s ≤ 79) :
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
  have hs79 : (10 : ℚ) ^ s ≤ 10 ^ (79 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hs_hi
  unfold STAmount.roundToExponent
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg (by rw [hz]; exact Bool.false_ne_true),
    if_neg (not_le.mpr hexp)]
  have hchk : STAmount.checked value.mNumericType kMinValue s value.negative mode =
      .ok ⟨.fractional, kMinValue, s, value.mIsNegative⟩ := by
    rw [hc.is_fractional]
    exact STAmount.checked_reference s value.mIsNegative mode hs_lo (by omega)
  rw [hchk]
  simp only []
  set refA : STAmount := ⟨.fractional, kMinValue, s, value.mIsNegative⟩ with hrefA_def
  have hcr : refA.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ s; omega, by show s ≤ 80; omega⟩
  have hrefa : |refA.toRat| = 10 ^ 15 * 10 ^ s := by
    rw [STAmount.abs_toRat]
    show (kMinValue.toNat : ℚ) * 10 ^ s = _
    rw [hkMin]; push_cast; ring
  have hva := STAmount.abs_lt_of_exponent_lt value s hc h_ev
  -- value and reference share a sign, so the sum is their sizes added
  have hsame : |value.toRat + refA.toRat| = |value.toRat| + |refA.toRat| := by
    cases hn : value.mIsNegative
    · have h1 : 0 ≤ value.toRat := by rw [STAmount.toRat_of_nonneg value hn]; positivity
      have h2 : 0 ≤ refA.toRat := by rw [STAmount.toRat_of_nonneg refA hn]; positivity
      rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg (by linarith)]
    · have h1 : value.toRat ≤ 0 := by
        rw [STAmount.toRat_of_neg value hn]
        have : (0 : ℚ) ≤ (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := by positivity
        linarith
      have h2 : refA.toRat ≤ 0 := by
        rw [STAmount.toRat_of_neg refA hn]
        have : (0 : ℚ) ≤ (refA.mValue.toNat : ℚ) * 10 ^ refA.mOffset := by positivity
        linarith
      rw [abs_of_nonpos h1, abs_of_nonpos h2, abs_of_nonpos (by linarith)]
      ring
  have h1594 : (10 : ℚ) ^ 15 * 10 ^ s ≤ 10 ^ 94 := by
    have : (10 : ℚ) ^ 15 * 10 ^ s ≤ 10 ^ 15 * 10 ^ (79 : ℤ) := mul_le_mul_of_nonneg_left hs79 (by norm_num)
    linarith [show (10 : ℚ) ^ 15 * 10 ^ (79 : ℤ) = 10 ^ 94 by norm_num]
  obtain ⟨sum, hsum⟩ : ∃ sum, STAmount.operator_add value refA mode = .ok sum :=
    STAmount.operator_add_iou_ok value refA mode hc hcr
      (STAmount.lift_add_exponent_le value refA mode hc hcr (by
        rw [hsame, hrefa]
        nlinarith [abs_nonneg value.toRat]))
  rw [hsum]
  simp only []
  obtain ⟨hsnt, hscz⟩ := STAmount.operator_add_fczr value refA sum mode ⟨hc.is_fractional, Or.inl hc⟩ hsum
  unfold STAmount.operator_sub
  have h_negRef : refA.operator_neg = ⟨.fractional, kMinValue, s, !value.mIsNegative⟩ := by
    rw [STAmount.operator_neg_of_ne refA (by show kMinValue ≠ 0; decide)]
  rw [h_negRef]
  set negRef : STAmount := ⟨.fractional, kMinValue, s, !value.mIsNegative⟩ with hnegRef_def
  have hcneg : negRef.IOUCanonical :=
    ⟨rfl, by show 10 ^ 15 ≤ kMinValue.toNat; omega, by show kMinValue.toNat < 10 ^ 16; omega,
      by show (-96 : ℤ) ≤ s; omega, by show s ≤ 80; omega⟩
  have hnega : |negRef.toRat| = 10 ^ 15 * 10 ^ s := by
    rw [STAmount.abs_toRat]
    show (kMinValue.toNat : ℚ) * 10 ^ s = _
    rw [hkMin]; push_cast; ring
  rcases hscz with hcs | hz0
  · -- the sum is at most twice its true value in size
    have hsne : sum.mValue ≠ 0 := by
      intro h0
      have h1 : sum.mValue.toNat = 0 := by rw [h0]; rfl
      have := hcs.mant_lo
      omega
    have htne : value.toRat + refA.toRat ≠ 0 := by
      intro h0
      have : |value.toRat + refA.toRat| = 0 := by rw [h0, abs_zero]
      rw [hsame, hrefa] at this
      linarith [abs_nonneg value.toRat, mul_pos (show (0 : ℚ) < 10 ^ 15 by norm_num) hps]
    have hrw := STAmount.operator_add_iou_rounds_directed value refA sum mode hc hcr htne hsum hsne
    have hsb := RoundsWithin.abs_le_two (by
      have h1 : (11 : ℚ) / (2 ^ 63 - 18) ≤ 1 / 10 := by norm_num
      have h2 : (10 : ℚ) ^ (-15 : ℤ) ≤ 1 / 10 := by norm_num
      have h3 : (11 : ℚ) / (2 ^ 63 - 18) * (10 : ℚ) ^ (-15 : ℤ) ≤ 1 / 10 := by norm_num
      linarith) hrw
    rw [hsame, hrefa] at hsb
    exact STAmount.operator_add_iou_ok sum negRef mode hcs hcneg
      (STAmount.lift_add_exponent_le sum negRef mode hcs hcneg (by
        have := abs_add_le sum.toRat negRef.toRat
        rw [hnega] at this
        nlinarith [abs_nonneg value.toRat]))
  · -- a zero sum takes the negated reference
    unfold STAmount.operator_add
    have hcmp : STAmount.areComparable sum negRef = true := by
      unfold STAmount.areComparable; rw [hsnt]; rfl
    have hnz : (negRef.mValue == 0) = false := by
      rw [beq_eq_false_iff_ne]; show kMinValue ≠ 0; decide
    have hs0 : (sum.mValue == 0) = true := by rw [hz0]; rfl
    rw [hcmp, hnz, hs0]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hsnt]
    exact ⟨_, STAmount.checked_reference s _ mode hs_lo (by omega)⟩

/-- The grid points either side of a value are within one step of it. -/
private lemma grid_near (r p : ℚ) (hp : 0 < p) :
    |(⌊r / p⌋ : ℚ) * p - r| ≤ p ∧ |(⌈r / p⌉ : ℚ) * p - r| ≤ p := by
  have h1 := Int.floor_le (r / p)
  have h2 := Int.lt_floor_add_one (r / p)
  have h3 := Int.le_ceil (r / p)
  have h4 := Int.ceil_lt_add_one (r / p)
  have e : r / p * p = r := div_mul_cancel₀ r hp.ne'
  constructor
  · rw [abs_le]
    constructor
    · nlinarith [mul_lt_mul_of_pos_right h2 hp]
    · nlinarith [mul_le_mul_of_nonneg_right h1 hp.le]
  · rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]
    · nlinarith [mul_lt_mul_of_pos_right h4 hp]

/-- A rounding onto the grid of `10^s` is within one step of the value. -/
private lemma RoundsToRepresentableAt.abs_sub_le {r : STAmount} {t : ℚ} {s : ℤ} {mode : rounding_mode}
    (h : RoundsToRepresentableAt r t s mode) : |r.toRat - t| ≤ 10 ^ s := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  obtain ⟨hf, hc⟩ := grid_near t (10 ^ s) hp
  unfold RoundsToRepresentableAt at h
  cases mode with
  | to_nearest =>
    rcases h with h | h
    · change r.toRat = _ at h; rw [h]; exact hf
    · change r.toRat = _ at h; rw [h]; exact hc
  | upward => change r.toRat = _ at h; rw [h]; exact hc
  | downward => change r.toRat = _ at h; rw [h]; exact hf
  | towards_zero =>
    change r.toRat = _ at h
    rw [h]
    split_ifs
    · exact hf
    · exact hc

/-- A number below `10^90` in size rounds to an IOU amount at a scale in `[-96, 79]`, in every mode, within one
unit at that scale of twice its size. -/
lemma STAmount.roundToNumericType_frac_ok_abs (x : Number) (mode : rounding_mode) (s : Int) (hx : x.isNormalized)
    (hlt : |x.toRat| < 10 ^ 90) (hs : -96 ≤ s ∧ s ≤ 79) :
    ∃ y, STAmount.roundToNumericType .fractional x mode (some s) = .ok y ∧ y.isNormalized ∧
      |y.toRat| ≤ 2 * |x.toRat| + 10 ^ s := by
  obtain ⟨ret, hret, hretf⟩ := STAmount.ofNumber_fractional_ok_fczr x mode hx hlt
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  have hretb : |ret.toRat| ≤ 2 * |x.toRat| := by
    rcases hretf.2 with hcr | hz
    · have hrne : ret.mValue ≠ 0 := by
        intro h0
        have h1 : ret.mValue.toNat = 0 := by rw [h0]; rfl
        have := hcr.mant_lo
        omega
      by_cases hm : x.mantissa_ = 0
      · exfalso
        rw [Number.eq_zero_of_mantissa_zero x hx hm, STAmount.ofNumber_fractional_zero] at hret
        obtain rfl := (Except.ok.inj hret)
        exact hrne rfl
      obtain ⟨hlo, hhi⟩ := hx.mantissaBounds_nat hm
      have he := Number.exponent_lt_of_abs_lt x hx hm 72 (by norm_num; exact hlt)
      obtain ⟨hw, -⟩ := STAmount.ofNumber_iou_within_ulp .fractional x mode ret rfl hlo hhi
        (Number.exponent_ge_min x hx hm) (by unfold maxExponent; omega) hret hrne
      have hxa := abs_toRat_eq x
      have hml : (10 : ℚ) ^ 18 ≤ (x.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
      have hpe : (10 : ℚ) ^ (x.exponent_ + 3) = 1000 * 10 ^ x.exponent_ := by
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
      have hpp : (0 : ℚ) < 10 ^ x.exponent_ := zpow_pos (by norm_num) _
      have hulp : (10 : ℚ) ^ (x.exponent_ + 3) ≤ |x.toRat| := by
        rw [hpe, hxa]; nlinarith
      have := abs_sub_abs_le_abs_sub ret.toRat x.toRat
      linarith
    · have : ret.toRat = 0 := by
        rw [STAmount.toRat_eq_number]
        exact Number.toRat_eq_zero_of_mantissa_zero _ hz
      rw [this, abs_zero]; positivity
  obtain ⟨rd, hrd⟩ : ∃ rd, STAmount.roundToExponent ret s mode = .ok rd := by
    rcases hretf.2 with hcr | hz
    · exact STAmount.roundToExponent_ok_abs ret s mode hcr hs.1 hs.2
    · exact ⟨ret, STAmount.roundToExponent_eq_self ret s _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz])))⟩
  have hrdf := STAmount.roundToExponent_fczr ret rd s mode hretf hrd
  have hrdb : |rd.toRat| ≤ |ret.toRat| + 10 ^ s := by
    have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
    by_cases hrz : rd.mValue = 0
    · have : rd.toRat = 0 := by
        rw [STAmount.toRat_eq_number]
        exact Number.toRat_eq_zero_of_mantissa_zero _ hrz
      rw [this, abs_zero]; positivity
    rcases hretf.2 with hcr | hz
    · have h := (STAmount.roundToExponent_rounded ret rd s mode hcr (by omega) (by omega) hrz hrd).abs_sub_le
      have := abs_sub_abs_le_abs_sub rd.toRat ret.toRat
      linarith
    · rw [STAmount.roundToExponent_eq_self ret s _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz])))] at hrd
      obtain rfl := Except.ok.inj hrd
      linarith
  obtain ⟨y, hy, hyv⟩ : ∃ y, rd.toNumber mode = .ok y ∧ y.toRat = rd.toRat := by
    rcases hrdf.2 with hcd | hz
    · exact ⟨_, STAmount.toNumber_iou_canonical rd mode hcd, lift_toRat rd hcd.mant_hi⟩
    · have hfr : rd.integral = false := by unfold STAmount.integral; rw [hrdf.1]; rfl
      refine ⟨Number.zero, STAmount.toNumber_zero_fractional rd mode hfr hz, ?_⟩
      rw [Number.toRat_zero, STAmount.toRat_eq_number]
      exact (Number.toRat_eq_zero_of_mantissa_zero _ hz).symm
  have hok : STAmount.roundToNumericType .fractional x mode (some s) = .ok y := by
    unfold STAmount.roundToNumericType
    rw [hret]
    simp only [hret_int, Bool.false_eq_true, ↓reduceIte]
    rw [hrd]
    exact hy
  refine ⟨y, hok, STAmount.roundToNumericType_isNormalized _ _ _ _ _ hok, ?_⟩
  rw [hyv]
  linarith

/-- `to_rep` of a signed integer of at most `maxRep` returns it. -/
private lemma Number.to_rep_unchecked_zero (neg : Bool) (m : UInt64) (mode : rounding_mode)
    (hm : m.toNat ≤ maxRep.toNat) :
    (Number.unchecked neg m 0).to_rep mode = .ok (if neg then -m.toInt64 else m.toInt64) := by
  have hmaxlt : m.toNat < 2 ^ 63 := by
    have h63 : maxRep.toNat = 2 ^ 63 - 1 := by decide
    omega
  have hnpre : ¬ (maxRep < m) := by rw [UInt64.lt_iff_toNat_lt]; omega
  have hmant : (Number.unchecked neg m 0).mantissa = (if neg then -m.toInt64 else m.toInt64) := by
    simp only [Number.mantissa, Number.unchecked, gt_iff_lt, if_neg hnpre]
  have hexp : (Number.unchecked neg m 0).exponent = 0 := by
    simp only [Number.exponent, Number.unchecked, gt_iff_lt, if_neg hnpre]
  have hneg_ : (Number.unchecked neg m 0).negative_ = neg := rfl
  unfold Number.to_rep
  simp only [hmant, hexp, hneg_]
  by_cases hz : (if neg then -m.toInt64 else m.toInt64) == 0
  · rw [if_pos hz, beq_iff_eq.mp hz]
  · rw [if_neg hz]
    have hmag : (if neg then -(if neg then -m.toInt64 else m.toInt64)
        else (if neg then -m.toInt64 else m.toInt64)) = m.toInt64 := by
      cases neg <;> simp
    rw [hmag]
    simp only [lt_irrefl, if_false, ge_iff_le, le_refl, if_true]
    have hgrow : Number.to_rep.grow m.toInt64 0 = .ok m.toInt64 := by
      rw [Number.to_rep.grow]; simp
    rw [hgrow]
    simp only
    have hu64 : m.toInt64.toUInt64.toNat ≤ maxRep.toNat := by
      have : m.toInt64.toUInt64 = m := rfl
      rw [this]; exact hm
    have h_g0_empty : (if neg then Guard.new.set_negative else Guard.new).empty = true := by
      cases neg <;> decide
    rw [pushOverflow_noop_of_le_maxRep_of_empty hu64 _ mode h_g0_empty, start_guard_round]
    rw [if_neg (show ¬ ((-2 : Int) == 1 || (-2 : Int) == 0 && m.toInt64 % 2 == 1) = true from by
      simp)]
    rw [if_neg (show ¬ (maxRep.toInt64 < m.toInt64 ∧ m.toInt64 < maxRepUp.toInt64) from by
      intro hc
      have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
      rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide,
          UInt64.toInt64_toInt_of_lt m hmaxlt] at hlt
      omega)]

/-- A negative whole number of at most the maximum of an integral asset packs into it. -/
private lemma STAmount.checked_integral_neg_ok (nt : NumericType) (v : UInt64) (mode : rounding_mode)
    (hnt : nt.isIntegral = true) (hmo : (0 : Int) ≤ nt.maxOffset) (hv : v.toNat ≤ nt.maxValue.toNat)
    (hmr : nt.maxValue.toNat ≤ maxRep.toNat) :
    ∃ a, STAmount.checked nt v 0 true mode = .ok a ∧ (a.mValue = 0 ∨ a.mValue = v) := by
  unfold STAmount.checked STAmount.canonicalize
  have hint : (STAmount.unchecked nt v 0 true).integral = true := hnt
  rw [if_pos hint]
  by_cases hz : ((STAmount.unchecked nt v 0 true).mValue == 0 ||
      decide ((STAmount.unchecked nt v 0 true).mOffset ≤ -20)) = true
  · rw [if_pos hz]; exact ⟨_, rfl, Or.inl rfl⟩
  rw [if_neg hz, if_neg (show ¬ (STAmount.unchecked nt v 0 true).mOffset >
      (STAmount.unchecked nt v 0 true).mNumericType.maxOffset from by
    show ¬ (0 : Int) > nt.maxOffset; omega)]
  have hvr : v.toNat ≤ maxRep.toNat := le_trans hv hmr
  have hlt : v.toNat < 2 ^ 63 := by
    have h63 : maxRep.toNat = 2 ^ 63 - 1 := by decide
    omega
  simp only [IntAmount.ofNumber, STAmount.unchecked]
  rw [Number.to_rep_unchecked_zero true v mode hvr]
  simp only [if_true]
  have habs : (-v.toInt64).toInt.natAbs.toUInt64 = v := by
    have := signed_mantissa_toInt true v hlt
    simp only [if_true] at this
    rw [this]
    simp only [neg_mul, one_mul, Int.natAbs_neg, Int.natAbs_natCast]
    exact UInt64.ofNat_toNat
  rw [habs, if_neg (by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
    omega)]
  exact ⟨_, rfl, Or.inr rfl⟩

/-- A number a unit below the maximum of XRP or an MPT in size rounds to that asset, in every mode and at any
scale, within one of twice its size. -/
lemma STAmount.roundToNumericType_integral_ok_abs (nt : NumericType) (x : Number) (mode : rounding_mode)
    (s : Option Int) (hnt : nt = .native ∨ nt = .int64) (hx : x.isNormalized)
    (hmax : |x.toRat| + 1 ≤ nt.maxValue.toNat) :
    ∃ y, STAmount.roundToNumericType nt x mode s = .ok y ∧ y.isNormalized ∧ |y.toRat| ≤ 2 * |x.toRat| + 1 := by
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hmo : (0 : Int) ≤ nt.maxOffset := by rcases hnt with rfl | rfl <;> decide
  have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
  have hmq : (nt.maxValue.toNat : ℚ) ≤ 2 ^ 63 - 1 := by
    have : (nt.maxValue.toNat : ℚ) ≤ maxRep.toNat := by exact_mod_cast hmr
    have hm : (maxRep.toNat : ℚ) = 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
    linarith
  obtain ⟨ret, hret, hretb⟩ : ∃ ret, STAmount.ofNumber nt x mode = .ok ret ∧ |ret.toRat| ≤ |x.toRat| + 1 := by
    by_cases hneg : x.negative_ = false
    · have h0 : 0 ≤ x.toRat := Number.toRat_nonneg_of_nonnegative x hneg
      rw [abs_of_nonneg h0] at hmax
      obtain ⟨ret, hret⟩ := STAmount.ofNumber_integral_ok_of_lt nt x mode hint hmo hx h0 (by linarith) hmax
      have hw := STAmount.ofNumber_integral_within_one nt x mode ret hint hx hneg hret
      refine ⟨ret, hret, ?_⟩
      rw [abs_of_nonneg h0]
      have := abs_sub_abs_le_abs_sub ret.toRat x.toRat
      rw [abs_of_nonneg h0] at this
      linarith
    · have hneg' : x.negative_ = true := by simpa using hneg
      have hm0 : x.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_negative x hx hneg'
      set w := x.operator_neg with hw_def
      have hwn : w.isNormalized := Number.operator_neg_isNormalized x hx
      have hwneg : w.negative_ = false := by rw [Number.operator_neg_negative_of_ne x hm0, hneg']; rfl
      have hwv : w.toRat = -x.toRat := Number.toRat_neg x
      have hx0 : x.toRat < 0 := Number.toRat_neg_of_negative' x hneg' hm0
      rw [abs_of_neg hx0] at hmax ⊢
      obtain ⟨r, hr, hr0, hru64, -⟩ := STAmount.ofNumber_integral_reduce nt w mode hint hwn hwneg (by
        rw [hwv]; linarith)
      have hwr := to_rep_within_one w mode r hwn hr
      rw [hwv] at hwr
      have hrn : (r.toUInt64.toNat : ℤ) = r.toInt := toUInt64_toNat_of_nonneg r hr0
      have hrv : r.toUInt64.toNat ≤ nt.maxValue.toNat := by
        have h1 : (r.toInt : ℚ) < nt.maxValue.toNat := by have := (abs_lt.mp hwr).2; linarith
        have h2 : r.toInt < nt.maxValue.toNat := by exact_mod_cast h1
        omega
      obtain ⟨a, ha, hav⟩ := STAmount.checked_integral_neg_ok nt r.toUInt64 mode hint hmo hrv hmr
      have hsig : decide (x.signum < 0) = true := by
        rw [decide_eq_true_eq, (signum_eq_neg_one_iff x hx).mpr hx0]
        norm_num
      have heq : STAmount.ofNumber nt x mode = STAmount.checked nt r.toUInt64 0 true mode := by
        unfold STAmount.ofNumber
        rw [if_pos hint]
        simp only [hsig, if_true]
        rw [← hw_def, hr]
      refine ⟨a, by rw [heq, ha], ?_⟩
      have hca := (STAmount.ofNumber_integral_canonical nt x mode a hint (by rw [heq, ha])).1
      rw [STAmount.abs_toRat, hca.offset_zero, zpow_zero, mul_one]
      rcases hav with h | h
      · rw [h]; simp; linarith
      · rw [h]
        have : ((r.toUInt64.toNat : ℕ) : ℚ) = (r.toInt : ℚ) := by exact_mod_cast hrn
        rw [this]
        have := (abs_lt.mp hwr).2
        linarith
  obtain ⟨hc, hrnt⟩ := STAmount.ofNumber_integral_canonical nt x mode ret hint hret
  have hret_int : ret.integral = true := by unfold STAmount.integral; rw [hrnt]; exact hint
  obtain ⟨y, hy, hyv, hyn, -⟩ := STAmount.toNumber_integral_exact ret mode hc (by rw [hrnt]; exact hmr)
  have hok : STAmount.roundToNumericType nt x mode s = .ok y := by
    unfold STAmount.roundToNumericType
    rw [hret]
    cases s with
    | none => exact hy
    | some s => simp only [hret_int, ↓reduceIte]; exact hy
  refine ⟨y, hok, hyn, ?_⟩
  rw [hyv]
  linarith [abs_nonneg x.toRat]

end XRPL.Model.Protocol
