import XRPL.Properties.Lending.Loan.Common.NumberTotal
import XRPL.Properties.Protocol.STAmount.Common.STAmountToNumber
import XRPL.Properties.Protocol.STAmount.Common.OfNumberFacts
import XRPL.Properties.Lending.Loan.Common.RoundToNearest
import XRPL.Properties.Lending.Loan.Common.SetLawful

/-! # Rounding to an asset never fails within range

An IOU amount rounds to a scale in every mode, so a nonnegative number below `10^90` rounds to an IOU amount at
any scale in `[-96, 79]`. A nonnegative number a unit below the maximum of XRP or an MPT rounds to it too. -/

namespace XRPL.Model.Protocol

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

/-- A nonnegative number below `10^90` rounds to an IOU amount at a scale in `[-96, 79]`, in every mode. -/
lemma STAmount.roundToNumericType_frac_ok (x : Number) (mode : rounding_mode) (s : Int) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hlt : x.toRat < 10 ^ 90) (hs : -96 ≤ s ∧ s ≤ 79) :
    ∃ y, STAmount.roundToNumericType .fractional x mode (some s) = .ok y := by
  obtain ⟨ret, hret, hretf⟩ := STAmount.ofNumber_fractional_ok_fczr x mode hx (by rw [abs_of_nonneg h0]; exact hlt)
  have hret0 := STAmount.ofNumber_nonneg .fractional x mode ret hx (Number.negative_false_of_nonneg x hx h0) hret
  have hret_int : ret.integral = false := by unfold STAmount.integral; rw [hretf.1]; rfl
  obtain ⟨rd, hrd⟩ : ∃ rd, STAmount.roundToExponent ret s mode = .ok rd := by
    rcases hretf.2 with hc' | hz
    · exact STAmount.roundToExponent_ok_any ret s mode hc' (STAmount.mIsNegative_false_of_nonneg ret hret0 (by
        intro h0; have := hc'.mant_lo; rw [h0] at this; exact absurd this (by decide))) hs.1 hs.2
    · exact ⟨ret, STAmount.roundToExponent_eq_self ret s _ (Or.inr (Or.inl (by simp [STAmount.isZero, hz])))⟩
  have hrdf := STAmount.roundToExponent_fczr ret rd s mode hretf hrd
  obtain ⟨y, hy, -, -⟩ := hrdf.toNumber_ok mode
  refine ⟨y, ?_⟩
  unfold STAmount.roundToNumericType
  rw [hret]
  simp only [hret_int, Bool.false_eq_true, ↓reduceIte]
  rw [hrd]
  exact hy

/-- A nonnegative number a unit below the maximum of XRP or an MPT rounds to that asset, in every mode and
at any scale. -/
lemma STAmount.roundToNumericType_integral_ok (nt : NumericType) (x : Number) (mode : rounding_mode)
    (s : Option Int) (hnt : nt = .native ∨ nt = .int64) (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmax : x.toRat + 1 ≤ nt.maxValue.toNat) :
    ∃ y, STAmount.roundToNumericType nt x mode s = .ok y := by
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hmo : (0 : Int) ≤ nt.maxOffset := by rcases hnt with rfl | rfl <;> decide
  have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
  have hcap : x.toRat ≤ 2 ^ 63 - 2 := by
    have : (nt.maxValue.toNat : ℚ) ≤ maxRep.toNat := by exact_mod_cast hmr
    have hm : (maxRep.toNat : ℚ) = 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
    linarith
  obtain ⟨ret, hret⟩ := STAmount.ofNumber_integral_ok_of_lt nt x mode hint hmo hx h0 hcap hmax
  obtain ⟨hc, hrnt⟩ := STAmount.ofNumber_integral_canonical nt x mode ret hint hret
  have hret_int : ret.integral = true := by
    unfold STAmount.integral; rw [hrnt]; exact hint
  obtain ⟨y, hy, -, -, -⟩ := STAmount.toNumber_integral_exact ret mode hc (by rw [hrnt]; exact hmr)
  refine ⟨y, ?_⟩
  unfold STAmount.roundToNumericType
  rw [hret]
  cases s with
  | none => exact hy
  | some s => simp only [hret_int, ↓reduceIte]; exact hy

/-- A downward credit of a nonnegative delta onto a nonnegative IOU amount never throws while their sum is
below `10^89`, at a base exponent in `[-81, 79]`. A sum too big for the base exponent rounds at a coarser one. -/
lemma sumRoundAndSubtract_frac_downward_ok_any (A c : Number) (b : Int) (hA : A.isNormalized) (hc : c.isNormalized)
    (hA0 : 0 ≤ A.toRat) (hc0 : 0 ≤ c.toRat) (hb : -81 ≤ b ∧ b ≤ 79) (hlt : A.toRat + c.toRat < 10 ^ 89) :
    ∃ st, sumRoundAndSubtract A c b .fractional .downward = .ok st ∧ st.FracCanonZero := by
  have hε := Number.nearestError_pos
  have hε' := Number.nearestError_le
  -- the exponent of the sum, at most `79`
  obtain ⟨s0, hs0⟩ := Number.operator_add_ok_of_lt A c .to_nearest hA hc hA0 (by linarith) hc0 (by linarith)
  have hs0n := operator_add_isNormalized_to_nearest_sz _ _ _ hA hc hs0
  have hs00 : 0 ≤ s0.toRat := operator_add_nonneg _ _ _ hA hc hs0 (by linarith)
  have hs0lt : s0.toRat < 10 ^ 90 := by
    have := (Number.add_near _ _ _ hA hc hs0).le (by linarith)
    nlinarith
  obtain ⟨e, hex⟩ : ∃ e, numberExponent s0 b .fractional = .ok e := by
    unfold numberExponent
    by_cases hz : s0.operator_eq Number.zero = true
    · rw [if_pos hz]; exact ⟨b, rfl⟩
    · rw [if_neg hz]
      obtain ⟨st, hst, -⟩ := STAmount.ofNumber_fractional_ok_fczr s0 .downward hs0n
        (by rw [abs_of_nonneg hs00]; exact hs0lt)
      rw [hst]
      exact ⟨_, rfl⟩
  have heb : b ≤ e := numberExponent_ge _ _ _ _ hex
  have he79 : e ≤ 79 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨-, hbig⟩ := numberExponent_frac_lower s0 b e hs0n hs00 (by omega) hex (by omega)
    have h1 : (10 : ℚ) ^ (90 : ℤ) ≤ 10 ^ (e + 15) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (10 : ℚ) ^ (90 : ℤ) = 10 ^ 90 := by norm_num
    linarith
  have hpse : postSumExponent A c b .fractional = .ok e := by
    unfold postSumExponent; rw [hs0, ok_bind]; exact hex
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
  obtain ⟨sm', hround⟩ := STAmount.roundToNumericType_frac_ok sm .downward e hsmn hsm0 (by linarith)
    ⟨by omega, he79⟩
  have hsm'n := STAmount.roundToNumericType_isNormalized _ _ _ _ _ hround
  have hsm'0 := STAmount.roundToNumericType_some_nonneg _ _ _ _ _ hsmn hsm0 (Or.inr (Or.inr rfl))
    ⟨by omega, by omega⟩ hround
  have hsm'le := XRPL.Model.Lending.STAmount.roundToNumericType_frac_downward_le _ _ _ hsmn hsm0
    ⟨by omega, by omega⟩ hround
  obtain ⟨d, hd⟩ := Number.operator_sub_ok_of_abs sm' A .downward hsm'n hA
    (by rw [abs_of_nonneg hsm'0]; linarith [show (10 : ℚ) ^ 89 < 10 ^ 200 by norm_num])
    (by rw [abs_of_nonneg hA0]; linarith [show (10 : ℚ) ^ 89 < 10 ^ 200 by norm_num])
  have hdn : d.isNormalized := Number.operator_add_isNormalized_any _ _ _ _ hsm'n
    (Number.operator_neg_isNormalized A hA) hd
  have hdlt : |d.toRat| < 10 ^ 90 := by
    by_cases h0 : d.mantissa_ = 0
    · rw [Number.toRat_eq_zero_of_mantissa_zero d h0, abs_zero]; norm_num
    obtain ⟨l, hl, hv⟩ := operator_add_rounded_downward sm' A.operator_neg d hsm'n
      (Number.operator_neg_isNormalized A hA) hd h0
    rw [Number.toRat_neg] at hl
    have hle : d.toRat ≤ sm'.toRat + -A.toRat := by rw [hv]; exact Number.lower_le _ l hl
    have hge : -A.toRat ≤ d.toRat := by
      rw [hv]
      have := Number.lower_tight _ l hl A.operator_neg (Number.operator_neg_isNormalized A hA)
        (by rw [Number.toRat_neg]; linarith)
      rwa [Number.toRat_neg] at this
    rw [abs_lt]
    constructor <;> nlinarith
  obtain ⟨st, hst, hstf⟩ := STAmount.ofNumber_fractional_ok_fczr d .downward hdn hdlt
  refine ⟨st, ?_, hstf⟩
  unfold sumRoundAndSubtract
  rw [if_neg (by decide)]
  show (pure PUnit.unit >>= fun _ => (do
      let exponent ← postSumExponent A c b NumericType.fractional
      let sum ← A.operator_add c rounding_mode.downward
      let sum' ← STAmount.roundToNumericType NumericType.fractional sum rounding_mode.downward (some exponent)
      let amountDelta' ← sum'.operator_sub A rounding_mode.downward
      STAmount.ofNumber NumericType.fractional amountDelta' rounding_mode.downward)) = _
  rw [show (pure PUnit.unit : Except Error PUnit) = .ok PUnit.unit from rfl, ok_bind, hpse, ok_bind, hsm, ok_bind,
    hround, ok_bind, show sm'.operator_sub A .downward = .ok d from hd, ok_bind, hst]

/-- A downward credit onto an XRP or MPT amount never throws while the delta is nonnegative and a unit below
the asset's maximum. -/
lemma sumRoundAndSubtract_integral_ok (A c : Number) (b : Int) (nt : NumericType) (mode : rounding_mode)
    (hnt : nt = .native ∨ nt = .int64) (hc : c.isNormalized) (hc0 : 0 ≤ c.toRat)
    (hmax : c.toRat + 1 ≤ nt.maxValue.toNat) :
    ∃ st, sumRoundAndSubtract A c b nt mode = .ok st := by
  have hint : nt.isIntegral = true := by rcases hnt with rfl | rfl <;> rfl
  have hmo : (0 : Int) ≤ nt.maxOffset := by rcases hnt with rfl | rfl <;> decide
  have hmr : nt.maxValue.toNat ≤ maxRep.toNat := by rcases hnt with rfl | rfl <;> decide
  have hcap : c.toRat ≤ 2 ^ 63 - 2 := by
    have : (nt.maxValue.toNat : ℚ) ≤ maxRep.toNat := by exact_mod_cast hmr
    have hm : (maxRep.toNat : ℚ) = 2 ^ 63 - 1 := by rw [maxRep_val]; norm_num
    linarith
  obtain ⟨st, hst⟩ := STAmount.ofNumber_integral_ok_of_lt nt c mode hint hmo hc hc0 hcap hmax
  refine ⟨st, ?_⟩
  unfold sumRoundAndSubtract
  rw [if_pos hint, hst]
  rfl

end XRPL.Model.Protocol
