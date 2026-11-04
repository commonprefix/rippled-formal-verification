import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Vault.Proofs.Support.OfNumberFractional
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Protocol.Number.AtExponent
import XRPL.Properties.Protocol.Number.Add.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Totality
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Support.PostSumExponent
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Lending.Loan.Common.ManageCover
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.Common.TenthBips
import XRPL.Properties.Vault.Proofs.Support.VaultBalances
import XRPL.Properties.Lending.Loan.Common.ManageDefs

/-! # The cover a default pays always computes

On the base grid below `10^16` base units every step of the cover computation succeeds: the two rate products,
the rounding to the asset, and the credit floored onto the grid of AssetsAvailable. -/

namespace XRPL.Model.Protocol

open private STAmount.ofNumber_integral_reduce from XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality

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

/-- A nonzero downward sum of a nonnegative true value below `10^19` units at exponent `t` has its exponent at
most `t`. -/
private lemma add_downward_exponent_le (x y n : Number) (t : Int) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .downward = .ok n) (hn0 : n.mantissa_ ≠ 0) (h0 : 0 ≤ x.toRat + y.toRat)
    (ht : minExponent + 18 ≤ t) (hlt : x.toRat + y.toRat < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ t) :
    n.exponent_ ≤ t := by
  have hnn := operator_add_isNormalized _ _ _ .downward hx hy hok hn0
  obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward x y n hx hy hok hn0
  have hle : n.toRat ≤ x.toRat + y.toRat := by rw [hv]; exact Number.lower_le _ l hl
  have hge : 0 ≤ n.toRat := by
    rw [hv]
    have := Number.lower_tight _ l hl Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; exact h0)
    rwa [Number.toRat_zero] at this
  exact Number.exponent_le_of_toRat_lt n t hnn (Number.negative_false_of_nonneg n hnn hge) ht
    (lt_of_le_of_lt hle hlt)

/-- Rounding a nonnegative IOU amount down to a scale never throws, for a scale in `[-96, 79]`. -/
lemma STAmount.roundToExponent_downward_ok (value : STAmount) (s : Int) (hc : value.IOUCanonical)
    (hneg : value.mIsNegative = false) (hs_lo : -96 ≤ s) (hs_hi : s ≤ 79) :
    ∃ r, STAmount.roundToExponent value s .downward = .ok r := by
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
  have h1000 : (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ (s - 3) = 10 ^ 16 * 10 ^ s := by
    rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; field_simp
  unfold STAmount.roundToExponent
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg (by rw [hz]; exact Bool.false_ne_true),
    if_neg (not_le.mpr hexp)]
  have hchk : STAmount.checked value.mNumericType kMinValue s value.negative .downward =
      .ok ⟨.fractional, kMinValue, s, false⟩ := by
    rw [hc.is_fractional]
    show STAmount.checked .fractional kMinValue s value.mIsNegative .downward = _
    rw [hneg]
    exact STAmount.checked_reference s false .downward hs_lo (by omega)
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
  obtain ⟨sum, hsum⟩ : ∃ sum, STAmount.operator_add value refA .downward = .ok sum := by
    apply STAmount.operator_add_iou_ok value refA .downward hc hcr
    intro n hadd hn0
    have := add_downward_exponent_le _ _ n (s - 3)
      (lift_isNormalized _ _ _ hc.mant_lo hc.mant_hi (by have := hc.exp_lo; unfold minExponent; omega)
        (by have := hc.exp_hi; unfold maxExponent; omega))
      (lift_isNormalized _ _ _ hcr.mant_lo hcr.mant_hi (by show minExponent ≤ s - 3; unfold minExponent; omega)
        (by show s - 3 ≤ maxExponent; unfold maxExponent; omega))
      hadd hn0 (by rw [lift_toRat value hc.mant_hi, lift_toRat refA hcr.mant_hi, hrefv]; positivity)
      (by unfold minExponent; omega)
      (by rw [lift_toRat value hc.mant_hi, lift_toRat refA hcr.mant_hi, hrefv, h1000]; nlinarith)
    omega
  rw [hsum]
  simp only []
  have hrefeq : refA = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
    rw [hc.is_fractional, hneg]
  obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, -⟩ :=
    STAmount.roundToExponent_sum_spec value s .downward hc h_ev hs_lo (by omega) sum (by rw [← hrefeq]; exact hsum)
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
  apply STAmount.operator_add_iou_ok sum negRef .downward hc_sum hcneg
  intro n hadd hn0
  have hk : (k : ℚ) ≤ 10 ^ 15 := by exact_mod_cast hk_le
  have := add_downward_exponent_le _ _ n (s - 3)
    (lift_isNormalized _ _ _ hc_sum.mant_lo hc_sum.mant_hi
      (by have := hc_sum.exp_lo; unfold minExponent; omega) (by have := hc_sum.exp_hi; unfold maxExponent; omega))
    (lift_isNormalized _ _ _ hcneg.mant_lo hcneg.mant_hi (by show minExponent ≤ s - 3; unfold minExponent; omega)
      (by show s - 3 ≤ maxExponent; unfold maxExponent; omega))
    hadd hn0
    (by rw [lift_toRat sum hc_sum.mant_hi, lift_toRat negRef hcneg.mant_hi, hsumv, hnegv]; push_cast; nlinarith)
    (by unfold minExponent; omega)
    (by rw [lift_toRat sum hc_sum.mant_hi, lift_toRat negRef hcneg.mant_hi, hsumv, hnegv, h1000]; push_cast; nlinarith)
  omega

/-- A nonzero normalized `Number` below `10^(k + 18)` in size has its exponent below `k`. -/
lemma Number.exponent_lt_of_abs_lt (n : Number) (hn : n.isNormalized) (h0 : n.mantissa_ ≠ 0) (k : Int)
    (hlt : |n.toRat| < (10 : ℚ) ^ (k + 18)) : n.exponent_ < k := by
  obtain ⟨hlo, -⟩ := hn.mantissaBounds_nat h0
  rw [abs_toRat_eq n] at hlt
  have hm : (10 : ℚ) ^ (18 : ℕ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
  have h1 : (10 : ℚ) ^ (18 : ℕ) * 10 ^ n.exponent_ < 10 ^ (k + 18) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hm (zpow_pos (by norm_num) _).le) hlt
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ k)] at h1
  have h2 : (10 : ℚ) ^ n.exponent_ < 10 ^ k := by
    have : (10 : ℚ) ^ (18 : ℤ) = 10 ^ (18 : ℕ) := zpow_natCast 10 18
    rw [this] at h1
    exact lt_of_mul_lt_mul_left h1 (by positivity)
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h2

/-- A `Number` below `10^90` in size converts to an IOU amount, canonical or zero. -/
lemma STAmount.ofNumber_fractional_ok_fczr (n : Number) (mode : rounding_mode) (hn : n.isNormalized)
    (hlt : |n.toRat| < 10 ^ 90) :
    ∃ st, STAmount.ofNumber .fractional n mode = .ok st ∧ st.FracCanonZero := by
  by_cases hm : n.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero n hn hm, STAmount.ofNumber_fractional_zero]
    exact ⟨_, rfl, rfl, Or.inr rfl⟩
  obtain ⟨hlo, hhi⟩ := hn.mantissaBounds_nat hm
  have he := Number.exponent_lt_of_abs_lt n hn hm 72 (by norm_num; exact hlt)
  obtain ⟨st, hst⟩ := STAmount.ofNumber_fractional_ok n mode hlo hhi (Number.exponent_ge_min n hn hm)
    (by unfold cMaxOffset; omega)
  exact ⟨st, hst, STAmount.ofNumber_fractional_fczr n mode st hst⟩

/-- A fractional amount that is canonical or zero converts to a `Number` with exponent headroom. -/
lemma STAmount.FracCanonZero.toNumber_ok {s : STAmount} (h : s.FracCanonZero) (mode : rounding_mode) :
    ∃ n, s.toNumber mode = .ok n ∧ n.isNormalized ∧ n.exponent_ + 22 ≤ maxExponent := by
  rcases h.2 with hc | hz
  · refine ⟨_, STAmount.toNumber_iou_canonical s mode hc, STAmount.toNumber_iou_canonical_isNormalized s hc, ?_⟩
    show s.mOffset - 3 + 22 ≤ maxExponent
    have := hc.exp_hi
    unfold maxExponent; omega
  · have hfr : s.integral = false := by unfold STAmount.integral; rw [h.1]; rfl
    refine ⟨Number.zero, STAmount.toNumber_zero_fractional s mode hfr hz, Number.zero_isNormalized, ?_⟩
    show (-2147483648 : Int) + 22 ≤ maxExponent
    unfold maxExponent; norm_num

/-- A downward sum of a true value below `10^20` in size is below `10^90` in size. -/
private lemma add_downward_abs_lt (x y n : Number) (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .downward = .ok n) (hlt : |x.toRat + y.toRat| < 10 ^ 20) : |n.toRat| < 10 ^ 90 := by
  by_cases hn0 : n.mantissa_ = 0
  · rw [Number.toRat_eq_zero_of_mantissa_zero n hn0, abs_zero]; norm_num
  obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward x y n hx hy hok hn0
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (-10 ^ 18) 2 (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have habs := abs_lt.mp hlt
  have hle : n.toRat ≤ x.toRat + y.toRat := by rw [hv]; exact Number.lower_le _ l hl
  have hge : w.toRat ≤ n.toRat := by
    rw [hv]; exact Number.lower_tight _ l hl w hw (by rw [hwv]; push_cast; norm_num; linarith)
  rw [hwv] at hge
  push_cast at hge
  rw [abs_lt]; constructor <;> nlinarith

/-- `sumRoundAndSubtract` on an IOU never throws for a nonnegative amount and delta whose sum stays a base
unit below `10^16` base units. -/
lemma sumRoundAndSubtract_frac_downward_ok (A c : Number) (b : Int) (hA : A.isNormalized) (hc : c.isNormalized)
    (hA0 : 0 ≤ A.toRat) (hc0 : 0 ≤ c.toRat) (hb : -10 ≤ b ∧ b ≤ 0)
    (hlt : A.toRat + c.toRat ≤ 10 ^ 16 * 10 ^ b - 10 ^ b) :
    ∃ st, sumRoundAndSubtract A c b .fractional .downward = .ok st ∧ st.FracCanonZero := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hb.2
  have hT : A.toRat + c.toRat < 10 ^ 16 := by nlinarith
  have hpow16 : (10 : ℚ) ^ (16 + b) = (10 : ℚ) ^ 16 * 10 ^ b := by rw [zpow_add₀ (by norm_num)]; norm_num
  obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 16 - 1) b (by constructor <;> norm_num)
    ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩
  have hwv' : w.toRat = 10 ^ 16 * 10 ^ b - 10 ^ b := by rw [hwv]; push_cast; ring

  obtain ⟨s0, hs0⟩ := Number.operator_add_ok_of_lt A c .to_nearest hA hc hA0 (by linarith) hc0 (by linarith)
  have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hs0
  have hs0le : s0.toRat ≤ w.toRat :=
    operator_add_le_of_le_normalized _ _ _ _ hA hc hs0 hw (by rw [hwv']; exact hlt)
  have hs00 : 0 ≤ s0.toRat := operator_add_nonneg _ _ _ hA hc hs0 (by linarith)
  obtain ⟨e, he'⟩ : ∃ e, numberExponent s0 b .fractional = .ok e := by
    unfold numberExponent
    by_cases hz : s0.operator_eq Number.zero = true
    · rw [if_pos hz]; exact ⟨b, rfl⟩
    · rw [if_neg hz]
      obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr s0 .downward hs0n
        (by rw [abs_of_nonneg hs00]; nlinarith)
      rw [hst]
      exact ⟨_, rfl⟩
  have heb : e = b := by
    have hge := numberExponent_ge _ _ _ _ he'
    by_contra hne
    have hlt' : b < e := lt_of_le_of_ne hge (Ne.symm hne)
    obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 b e hs0n hs00 (by omega) he' hlt'
    have h1 : (10 : ℚ) ^ (16 + b) ≤ 10 ^ (e + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [hpow16] at h1
    linarith
  subst heb
  have he : postSumExponent A c e .fractional = .ok e := by
    unfold postSumExponent; rw [hs0, ok_bind]; exact he'

  obtain ⟨sm, hsm⟩ := Number.operator_add_ok_of_lt A c .downward hA hc hA0 (by linarith) hc0 (by linarith)
  have hsmn := Number.operator_add_isNormalized_any _ _ _ _ hA hc hsm
  have hsmle : sm.toRat ≤ A.toRat + c.toRat := by
    by_cases h0 : sm.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero sm h0]; linarith
    obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward A c sm hA hc hsm h0
    rw [hv]; exact Number.lower_le _ l hl
  have hsm0 : 0 ≤ sm.toRat := by
    by_cases h0 : sm.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero sm h0]
    obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward A c sm hA hc hsm h0
    rw [hv]
    have := Number.lower_tight _ l hl Number.zero Number.zero_isNormalized (by rw [Number.toRat_zero]; linarith)
    rwa [Number.toRat_zero] at this
  obtain ⟨ret, hret, hretf⟩ := STAmount.ofNumber_fractional_ok_fczr sm .downward hsmn
    (by rw [abs_of_nonneg hsm0]; nlinarith)
  have hretle : 0 ≤ ret.toRat ∧ ret.toRat ≤ sm.toRat := by
    by_cases hz : ret.mValue = 0
    · rw [STAmount.toRat_eq_zero_of_mValue_zero ret hz]; exact ⟨le_refl _, hsm0⟩
    · obtain ⟨h1, -, h2⟩ := STAmount.ofNumber_downward_floor_bounds .fractional sm ret hsmn
        (Number.negative_false_of_nonneg sm hsmn hsm0) hret hz
      exact ⟨h2, h1⟩
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  obtain ⟨rd, hrd, hrdle⟩ : ∃ rd, STAmount.roundToExponent ret e .downward = .ok rd ∧
      0 ≤ rd.toRat ∧ rd.toRat ≤ ret.toRat := by
    rcases hretf.2 with hc' | hz
    · obtain ⟨rd, hrd⟩ := STAmount.roundToExponent_downward_ok ret e hc'
        (STAmount.mIsNegative_false_of_nonneg ret hretle.1 (by
          intro h0; have := hc'.mant_lo; rw [h0] at this; exact absurd this (by decide)))
        (by omega) (by omega)
      exact ⟨rd, hrd, STAmount.roundToExponent_downward_nonneg ret rd e hc' (by omega) (by omega) hretle.1 hrd,
        STAmount.roundToExponent_downward_le ret rd e hc' (by omega) (by omega) hretle.1 hrd⟩
    · exact ⟨ret, STAmount.roundToExponent_eq_self ret e _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz]))),
        hretle.1, le_refl _⟩
  have hrdf := STAmount.roundToExponent_fczr ret rd e .downward hretf hrd
  obtain ⟨sm', hsm', hsm'n, hsm'e⟩ := hrdf.toNumber_ok .downward
  have hsm'v : sm'.toRat = rd.toRat := by
    rcases hrdf.2 with hc' | hz
    · rw [STAmount.toNumber_iou_canonical rd .downward hc', Except.ok.injEq] at hsm'
      rw [← hsm']; exact STAmount.toNumber_iou_canonical_toRat rd hc'
    · have hfr : rd.integral = false := by unfold STAmount.integral; rw [hrdf.1]; rfl
      rw [STAmount.toNumber_zero_fractional rd _ hfr hz, Except.ok.injEq] at hsm'
      rw [← hsm', Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero rd hz]
  have hround : STAmount.roundToNumericType .fractional sm .downward (some e) = .ok sm' := by
    unfold STAmount.roundToNumericType
    rw [hret]
    simp only [hret_int, Bool.false_eq_true, ↓reduceIte]
    rw [hrd]
    exact hsm'

  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_exp sm' A .downward hsm'n hA hsm'e
    (Number.exponent_headroom_of_lt A hA hA0 (by linarith))
  have hdn : d.isNormalized := Number.operator_add_isNormalized_any _ _ _ _ hsm'n
    (Number.operator_neg_isNormalized A hA) hd
  have hdlt : |d.toRat| < 10 ^ 90 :=
    add_downward_abs_lt sm' A.operator_neg d hsm'n (Number.operator_neg_isNormalized A hA) hd (by
      rw [Number.toRat_neg, hsm'v, abs_lt]; constructor <;> linarith)
  obtain ⟨st, hst, hstf⟩ := STAmount.ofNumber_fractional_ok_fczr d .downward hdn hdlt
  refine ⟨st, ?_, hstf⟩
  unfold sumRoundAndSubtract
  rw [if_neg (by decide)]
  show (pure PUnit.unit >>= fun _ => (do
      let exponent ← postSumExponent A c e NumericType.fractional
      let sum ← A.operator_add c rounding_mode.downward
      let sum' ← STAmount.roundToNumericType NumericType.fractional sum rounding_mode.downward (some exponent)
      let amountDelta' ← sum'.operator_sub A rounding_mode.downward
      STAmount.ofNumber NumericType.fractional amountDelta' rounding_mode.downward)) = _
  rw [show (pure PUnit.unit : Except Error PUnit) = .ok PUnit.unit from rfl, ok_bind, he, ok_bind, hsm, ok_bind,
    hround, ok_bind, show sm'.operator_sub A .downward = .ok d from hd, ok_bind, hst]

/-- A nonzero normalized `Number` at least `10^(k + 19)` in size has its exponent above `k`. -/
lemma Number.exponent_gt_of_abs_ge (n : Number) (hn : n.isNormalized) (h0 : n.mantissa_ ≠ 0) (k : Int)
    (hge : (10 : ℚ) ^ (k + 19) ≤ |n.toRat|) : k < n.exponent_ := by
  obtain ⟨-, hhi⟩ := hn.mantissaBounds_nat h0
  rw [abs_toRat_eq n] at hge
  have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hhi
  have h1 : (10 : ℚ) ^ (k + 19) < (10 : ℚ) ^ (19 : ℕ) * 10 ^ n.exponent_ :=
    lt_of_le_of_lt hge (mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _))
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), mul_comm ((10 : ℚ) ^ k)] at h1
  have h2 : (10 : ℚ) ^ k < 10 ^ n.exponent_ := by
    have : (10 : ℚ) ^ (19 : ℤ) = 10 ^ (19 : ℕ) := zpow_natCast 10 19
    rw [this] at h1
    exact lt_of_mul_lt_mul_left h1 (by positivity)
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp h2

/-- An upward rate of a value never throws, for a value below `10^20`, at least `10^L` when nonzero, and a
rate of at most 100%. The result is at most the value, and at least `10^(L - 5)` when nonzero. -/
lemma tenthBipsOfValue_upward_ok (d : Number) (rate : TenthBips32) (L : Int) (hd : d.isNormalized)
    (h0 : 0 ≤ d.toRat) (hlt : d.toRat < 10 ^ 20) (hL : -100 ≤ L) (hlo : d.mantissa_ ≠ 0 → (10 : ℚ) ^ L ≤ d.toRat)
    (hrate : rate.toNat ≤ 100000) :
    ∃ r, tenthBipsOfValue d rate .upward = .ok r ∧ r.isNormalized ∧ 0 ≤ r.toRat ∧ r.toRat ≤ d.toRat ∧
      (r.mantissa_ ≠ 0 → (10 : ℚ) ^ (L - 5) ≤ r.toRat) := by
  obtain ⟨hrn, hrv⟩ := TenthBips32.toNumber_facts rate
  obtain ⟨hun, huv⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  have hu5 : kTenthBipsPerUnity.toNumber.toRat = 100000 := by rw [huv]; rfl
  have hr5 : rate.toNumber.toRat ≤ 100000 := by rw [hrv]; exact_mod_cast hrate
  have hr0 : 0 ≤ rate.toNumber.toRat := by rw [hrv]; positivity
  have hu0 : kTenthBipsPerUnity.toNumber.mantissa_ ≠ 0 := by
    intro h; rw [Number.toRat_eq_zero_of_mantissa_zero _ h] at hu5; norm_num at hu5
  have huz : kTenthBipsPerUnity.toNumber.operator_eq Number.zero = false :=
    Number.operator_eq_zero_false_of_mantissa_ne _ hu0
  -- a zero value or a zero rate gives zero
  by_cases hd0 : d.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero d hd hd0]
    exact ⟨Number.zero, tenthBipsOfValue_zero rate, Number.zero_isNormalized, by rw [Number.toRat_zero],
      by rw [Number.toRat_zero], fun h => absurd rfl h⟩
  have hdz : d.operator_eq Number.zero = false := Number.operator_eq_zero_false_of_mantissa_ne _ hd0
  by_cases hrz : rate.toNumber.mantissa_ = 0
  · have hrzero : rate.toNumber = Number.zero := Number.eq_zero_of_mantissa_zero _ hrn hrz
    have hzz : Number.zero.operator_eq Number.zero = true :=
      (operator_eq_iff _ _ Number.zero_isNormalized Number.zero_isNormalized).mpr rfl
    refine ⟨Number.zero, ?_, Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; exact h0,
      fun h => absurd rfl h⟩
    unfold tenthBipsOfValue
    dsimp only
    rw [hrzero]
    simp [Number.operator_mul, Number.operator_div, hdz, hzz, huz, bind, Except.bind, pure, Except.pure]
  have hd' : (10 : ℚ) ^ L ≤ d.toRat := hlo hd0
  have hrate1 : (1 : ℚ) ≤ rate.toNumber.toRat := by
    rw [hrv]
    have : rate.toNat ≠ 0 := by
      intro h; apply hrz
      by_contra hne
      have := Number.toRat_ne_zero_of_mantissa_ne_zero _ hne
      rw [hrv, h] at this; exact this rfl
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hde1 := Number.exponent_gt_of_abs_ge d hd hd0 (L - 19) (by rw [abs_of_nonneg h0]; simpa using hd')
  have hde2 := Number.exponent_lt_of_abs_lt d hd hd0 2 (by rw [abs_of_nonneg h0]; norm_num; exact hlt)
  have hre1 := Number.exponent_gt_of_abs_ge _ hrn hrz (-19) (by
    rw [abs_of_nonneg hr0]; norm_num; exact hrate1)
  have hre2 := Number.exponent_lt_of_abs_lt _ hrn hrz (-8) (by rw [abs_of_nonneg hr0]; norm_num; linarith)
  obtain ⟨pr, hpr⟩ := Number.operator_mul_ok_of_normalized d rate.toNumber .upward hd hrn hd0 hrz
    (by unfold minExponent; omega) (by unfold maxExponent; omega)
  have hprn := Number.operator_mul_isNormalized _ _ _ _ hd hrn hpr
  have hneg : d.negative_ = false := Number.negative_false_of_nonneg d hd h0
  set W : Number := ⟨d.negative_, d.mantissa_, d.exponent_ + 5⟩ with hW
  have hWn : W.isNormalized := by
    rcases hd with hz | ⟨h1, h2, h3, h4, h5⟩
    · exact absurd (by rw [hz]; rfl) hd0
    · exact Or.inr ⟨h1, h2, h3, by show minExponent ≤ d.exponent_ + 5; omega,
        by show d.exponent_ + 5 ≤ maxExponent; unfold maxExponent; omega⟩
  have hWv : W.toRat = d.toRat * 100000 := by
    rw [Number.toRat_of_nonneg W hneg, Number.toRat_of_nonneg d hneg]
    show (d.mantissa_.toNat : ℚ) * 10 ^ (d.exponent_ + 5) = _
    rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num; ring
  have hprle : pr.toRat ≤ W.toRat := by
    by_cases hp0 : pr.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero pr hp0, hWv]; positivity
    obtain ⟨n, hn, hv⟩ := operator_mul_rounded_upward _ _ _ hd hrn hpr hp0
    rw [hv]; exact Number.upper_tight _ n hn W hWn (by rw [hWv]; nlinarith)
  by_cases hp0 : pr.mantissa_ = 0
  · have hpz : pr = Number.zero := Number.eq_zero_of_mantissa_zero _ hprn hp0
    have hzz : Number.zero.operator_eq Number.zero = true :=
      (operator_eq_iff _ _ Number.zero_isNormalized Number.zero_isNormalized).mpr rfl
    refine ⟨Number.zero, ?_, Number.zero_isNormalized, by rw [Number.toRat_zero], by rw [Number.toRat_zero]; exact h0,
      fun h => absurd rfl h⟩
    unfold tenthBipsOfValue
    dsimp only
    rw [hpr, ok_bind, hpz]
    simp [Number.operator_div, hzz, huz, pure, Except.pure]
  have hpr0 : 0 ≤ pr.toRat := by
    obtain ⟨n, hn, hv⟩ := operator_mul_rounded_upward _ _ _ hd hrn hpr hp0
    rw [hv]; exact le_trans (mul_nonneg h0 hr0) (Number.le_upper _ n hn)
  have hpe2 := Number.exponent_lt_of_abs_lt pr hprn hp0 7 (by
    rw [abs_of_nonneg hpr0]; norm_num; rw [hWv] at hprle; nlinarith)
  have hue1 := Number.exponent_gt_of_abs_ge _ hun hu0 (-14) (by rw [hu5]; norm_num)
  obtain ⟨r, hr⟩ := Number.operator_div_ok_of_normalized pr _ .upward hprn hun hp0 hu0
    (by unfold maxExponent; omega)
  have hok : tenthBipsOfValue d rate .upward = .ok r := by
    unfold tenthBipsOfValue
    dsimp only
    rw [hpr, ok_bind]
    exact hr
  have hrn' := Number.operator_div_isNormalized _ _ _ _ hprn hun hr
  obtain ⟨-, hr0'⟩ := tenthBipsOfValue_upward_facts d rate r hd h0 hok
  refine ⟨r, hok, hrn', hr0', ?_, ?_⟩
  · by_cases hrr : r.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero r hrr]; exact h0
    obtain ⟨n, hn, hv⟩ := operator_div_rounded_upward _ _ _ hprn hun hr hrr
    rw [hv]
    exact Number.upper_tight _ n hn d hd (by rw [hu5, div_le_iff₀ (by norm_num)]; linarith)
  · intro hrr
    obtain ⟨n, hn, hv⟩ := operator_div_rounded_upward _ _ _ hprn hun hr hrr
    obtain ⟨n', hn', hv'⟩ := operator_mul_rounded_upward _ _ _ hd hrn hpr hp0
    have h1 : d.toRat * rate.toNumber.toRat ≤ pr.toRat := by rw [hv']; exact Number.le_upper _ n' hn'
    have h2 : pr.toRat / 100000 ≤ r.toRat := by rw [hv, ← hu5]; exact Number.le_upper _ n hn
    have h3 : (10 : ℚ) ^ (L - 5) = 10 ^ L / 100000 := by
      rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
    rw [h3]
    have : (10 : ℚ) ^ L ≤ pr.toRat := by nlinarith
    calc (10 : ℚ) ^ L / 100000 ≤ pr.toRat / 100000 := by linarith
      _ ≤ r.toRat := h2

/-- An integral `ofNumber` of a nonnegative value at least one unit below the type's maximum never throws. -/
lemma STAmount.ofNumber_integral_ok_of_lt (nt : NumericType) (n : Number) (mode : rounding_mode)
    (hnt : nt.isIntegral = true) (hmaxoff : (0 : Int) ≤ nt.maxOffset) (hnorm : n.isNormalized)
    (h0 : 0 ≤ n.toRat) (hcap : n.toRat ≤ 2 ^ 63 - 2) (hmax : n.toRat + 1 ≤ nt.maxValue.toNat) :
    ∃ result, STAmount.ofNumber nt n mode = .ok result := by
  have hneg := Number.negative_false_of_nonneg n hnorm h0
  obtain ⟨r, hr, hr0, hru64, heq⟩ := STAmount.ofNumber_integral_reduce nt n mode hnt hnorm hneg (by linarith)
  rw [heq]
  have hw := to_rep_within_one n mode r hnorm hr
  have hrmax : r.toUInt64.toNat ≤ nt.maxValue.toNat := by
    have hnat : (r.toUInt64.toNat : ℤ) = r.toInt := toUInt64_toNat_of_nonneg r hr0
    have h1 : (r.toInt : ℚ) < nt.maxValue.toNat := by
      have := (abs_lt.mp hw).2; linarith
    have h2 : r.toInt < nt.maxValue.toNat := by exact_mod_cast h1
    omega
  obtain ⟨result, hres⟩ := STAmount.canonicalize_integral_ok_of_le
    (STAmount.unchecked nt r.toUInt64 0 false) mode hnt rfl rfl hru64 hrmax hmaxoff
  exact ⟨result, by rw [STAmount.checked]; exact hres⟩

end XRPL.Model.Protocol

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault RawVault)

/-- An XRP or MPT vault asset stores every whole number up to `10^16 + 1`, with a maxOffset of at least zero and a
largest value within a `Number` mantissa. -/
private lemma Vault.HoldsAsset.integral_room {v : Vault} (h : Vault.HoldsAsset v)
    (hint : v.numericType.isIntegral = true) :
    (10 : ℚ) ^ 16 + 1 ≤ v.numericType.maxValue.toNat ∧ (0 : Int) ≤ v.numericType.maxOffset ∧
      v.numericType.maxValue.toNat ≤ maxRep.toNat := by
  rcases h with h | h | h <;> rw [h] at hint ⊢
  · cases hint
  · refine ⟨?_, by decide, by decide⟩
    show (10 : ℚ) ^ 16 + 1 ≤ ((100000000000000000 : UInt64).toNat : ℚ)
    norm_num
    decide
  · refine ⟨?_, by decide, by decide⟩
    show (10 : ℚ) ^ 16 + 1 ≤ ((9223372036854775807 : UInt64).toNat : ℚ)
    norm_num
    decide

/-- The cover a default pays always computes on the base grid. The asset is XRP, an MPT or an IOU,
AssetsAvailable plus the loan's principal stays below `10^16` base units, and DebtTotal is whole base units. -/
lemma Loan.defaultCover_ok (loan : Loan) (v : Vault) (hasset : Vault.HoldsAsset v)
    (hnt : loan.broker.numericType = v.numericType) (hls : loan.loanScale = v.baseExponent)
    (haa : Number.AtExponent v.assetsAvailable.toRat v.baseExponent (10 ^ 16))
    (hroom : v.assetsAvailable.toRat + loan.principalOutstanding.toRat < 10 ^ 16 * (10 : ℚ) ^ v.baseExponent)
    (hdt : Number.AtExponent loan.broker.debtTotal.toRat v.baseExponent (10 ^ 16)) :
    ∃ dc, loan.defaultCover v = .ok dc := by
  set b := v.baseExponent with hbdef
  have hbase := v.baseExponent_bounds
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hp1 : (10 : ℚ) ^ b ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hbase.2.1
  obtain ⟨a, -, hav⟩ := haa
  obtain ⟨t, ht, htv⟩ := hdt
  obtain ⟨p, -, hpv⟩ := loan.grid.principalOutstanding_atExponent
  simp only [RawLoan.toExact] at hpv
  rw [hls] at hpv
  have hap : a + p < 10 ^ 16 := by
    have h1 : ((a + p : ℕ) : ℚ) * 10 ^ b < (10 ^ 16 : ℕ) * 10 ^ b := by
      push_cast; rw [add_mul, ← hav, ← hpv]; exact hroom
    exact_mod_cast lt_of_mul_lt_mul_right h1 hp.le
  have hroom' : v.assetsAvailable.toRat + loan.principalOutstanding.toRat ≤ 10 ^ 16 * 10 ^ b - 10 ^ b := by
    have h1 : (a : ℚ) + p ≤ 10 ^ 16 - 1 := by
      have : a + p ≤ 9999999999999999 := by omega
      have h2 : ((a + p : ℕ) : ℚ) ≤ 9999999999999999 := by exact_mod_cast this
      push_cast at h2; norm_num; linarith
    rw [hav, hpv]; nlinarith
  have hAA0 : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  have hPO0 : 0 ≤ loan.principalOutstanding.toRat := loan.exact.principalOutstanding_nonneg
  have hDT0 : 0 ≤ loan.broker.debtTotal.toRat := loan.broker.exact.debtTotal_nonneg
  have hbv := loan.broker.valid
  have hrmin : loan.broker.coverRateMinimum.toNat ≤ 100000 := by
    have := hbv.coverRateMinimum_cap; unfold maxCoverRate at this; exact UInt32.le_iff_toNat_le.mp this
  have hrliq : loan.broker.coverRateLiquidation.toNat ≤ 100000 := by
    have := hbv.coverRateLiquidation_cap; unfold maxCoverRate at this; exact UInt32.le_iff_toNat_le.mp this

  have ht16 : (t : ℚ) < 10 ^ 16 := by exact_mod_cast ht
  obtain ⟨mc, hmc, hmcn, hmc0, hmcle, hmclo⟩ := tenthBipsOfValue_upward_ok loan.broker.debtTotal
    loan.broker.coverRateMinimum (-10) loan.broker.wf.debtTotal_norm hDT0 (by rw [htv]; nlinarith) (by norm_num)
    (fun h0 => by
      rw [htv]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · exfalso; exact Number.toRat_ne_zero_of_mantissa_ne_zero _ h0 (by rw [htv, h]; simp)
        · exact h
      calc (10 : ℚ) ^ (-10 : ℤ) ≤ 10 ^ b := zpow_le_zpow_right₀ (by norm_num) hbase.1
        _ ≤ (t : ℚ) * 10 ^ b := le_mul_of_one_le_left hp.le (by exact_mod_cast ht1))
    hrmin
  obtain ⟨liq, hliq, hliqn, hliq0, -, -⟩ := tenthBipsOfValue_upward_ok mc loan.broker.coverRateLiquidation (-15)
    hmcn hmc0 (by rw [htv] at hmcle; nlinarith) (by norm_num) (fun h0 => by simpa using hmclo h0) hrliq

  obtain ⟨hm1, hm1n⟩ := Number.min_toRat liq loan.principalOutstanding hliqn loan.wf.principalOutstanding_norm
  obtain ⟨hm2, hm2n⟩ := Number.min_toRat _ loan.broker.coverAvailable hm1n loan.broker.wf.coverAvailable_norm
  obtain ⟨capped, hcapeq⟩ : ∃ x, x = Number.min (Number.min liq loan.principalOutstanding)
      loan.broker.coverAvailable := ⟨_, rfl⟩
  rw [← hcapeq] at hm2 hm2n
  have hcap0 : 0 ≤ capped.toRat := by
    rw [hm2, hm1]; exact le_min (le_min hliq0 hPO0) loan.broker.exact.coverAvailable_nonneg
  have hcapPO : capped.toRat ≤ loan.principalOutstanding.toRat := by
    rw [hm2, hm1]; exact min_le_of_left_le (min_le_right _ _)
  have hPO16 : loan.principalOutstanding.toRat < 10 ^ 16 := by nlinarith

  obtain ⟨c, hc⟩ : ∃ c, STAmount.roundToNumericType loan.broker.numericType capped .towards_zero = .ok c := by
    unfold STAmount.roundToNumericType
    cases hint : loan.broker.numericType.isIntegral
    · rw [NumericType.eq_fractional_of_not_integral hint]
      obtain ⟨ret, hret, hretf⟩ := STAmount.ofNumber_fractional_ok_fczr capped .towards_zero hm2n
        (by rw [abs_of_nonneg hcap0]; nlinarith)
      rw [hret]
      obtain ⟨n, hn, -⟩ := hretf.toNumber_ok .towards_zero
      exact ⟨n, hn⟩
    · obtain ⟨room, hoff, hmaxrep⟩ := hasset.integral_room (by rw [← hnt]; exact hint)
      rw [← hnt] at room hoff hmaxrep
      obtain ⟨ret, hret⟩ := STAmount.ofNumber_integral_ok_of_lt _ capped .towards_zero hint hoff hm2n hcap0
        (by nlinarith) (by nlinarith)
      rw [hret]
      obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ ret hint hret
      have hsmall : ret.mValue.toNat ≤ 2 ^ 63 - 1 := by
        have h1 := hic.in_range
        rw [hty] at h1
        have : maxRep.toNat = 2 ^ 63 - 1 := by decide
        omega
      obtain ⟨sn, hsn, -⟩ := STAmount.toNumber_integral_small_exact ret _ hic hsmall
      exact ⟨sn, hsn⟩
  obtain ⟨hc0, hcle, hcn⟩ := STAmount.roundToNumericType_towards_zero_le _ _ _ hm2n hcap0 hc

  obtain ⟨st, hst, dc, hdc⟩ : ∃ st, sumRoundAndSubtract v.assetsAvailable c b loan.broker.numericType .downward =
      .ok st ∧ ∃ dc, st.toNumber .to_nearest = .ok dc := by
    cases hint : loan.broker.numericType.isIntegral
    · rw [NumericType.eq_fractional_of_not_integral hint]
      obtain ⟨st, hst, hstf⟩ := sumRoundAndSubtract_frac_downward_ok v.assetsAvailable c b v.wf.assetsAvailable_norm
        hcn hAA0 hc0 ⟨hbase.1, hbase.2.1⟩ (by linarith)
      obtain ⟨n, hn, -⟩ := hstf.toNumber_ok .to_nearest
      exact ⟨st, hst, n, hn⟩
    · obtain ⟨room, hoff, hmaxrep⟩ := hasset.integral_room (by rw [← hnt]; exact hint)
      rw [← hnt] at room hoff hmaxrep
      obtain ⟨st, hof⟩ := STAmount.ofNumber_integral_ok_of_lt _ c .downward hint hoff hcn hc0
        (by nlinarith) (by nlinarith)
      refine ⟨st, ?_, ?_⟩
      · unfold sumRoundAndSubtract
        rw [if_pos hint, hof]
        rfl
      · obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ st hint hof
        have hsmall : st.mValue.toNat ≤ 2 ^ 63 - 1 := by
          have h1 := hic.in_range
          rw [hty] at h1
          have : maxRep.toNat = 2 ^ 63 - 1 := by decide
          omega
        obtain ⟨sn, hsn, -⟩ := STAmount.toNumber_integral_small_exact st _ hic hsmall
        exact ⟨sn, hsn⟩
  refine ⟨dc, ?_⟩
  show (tenthBipsOfValue loan.broker.debtTotal loan.broker.coverRateMinimum .upward >>= fun minimumCover =>
    tenthBipsOfValue minimumCover loan.broker.coverRateLiquidation .upward >>= fun liquidationAmount =>
    STAmount.roundToNumericType loan.broker.numericType
      (Number.min (Number.min liquidationAmount loan.principalOutstanding) loan.broker.coverAvailable)
      .towards_zero >>= fun coveredAmount =>
    sumRoundAndSubtract v.assetsAvailable coveredAmount v.baseExponent loan.broker.numericType .downward >>=
      fun defaultCovered => defaultCovered.toNumber .to_nearest) = _
  rw [hmc, ok_bind, hliq, ok_bind, ← hcapeq, hc, ok_bind, hst, ok_bind, hdc]

end XRPL.Model.Lending
