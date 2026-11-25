import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangePos

/-! # Proofs of the `STAmount.ofNumber` rounding theorems

`ofNumber` drops the sign of the Number, rounds the size in the mode and puts the sign back. The lemmas here
expose that size and how each mode rounds it. -/

namespace XRPL.Model.Protocol

/-- The size `ofNumber` rounds is the Number without its sign. It is normalized and has the same digits. -/
lemma STAmount.ofNumber_working_facts (n : Number) (hn : n.isNormalized) :
    (if decide (n.signum < 0) = true then n.operator_neg else n).isNormalized ∧
    (if decide (n.signum < 0) = true then n.operator_neg else n).negative_ = false ∧
    (if decide (n.signum < 0) = true then n.operator_neg else n).mantissa_ = n.mantissa_ ∧
    (if decide (n.signum < 0) = true then n.operator_neg else n).exponent_ = n.exponent_ ∧
    n.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) *
      (if decide (n.signum < 0) = true then n.operator_neg else n).toRat := by
  rw [Number.signum_neg_decide]
  by_cases hb : n.negative_ = true
  · have hm : n.mantissa_ ≠ 0 := by
      intro h0
      rw [Number.eq_zero_of_mantissa_zero n hn h0] at hb
      exact absurd hb (by decide)
    rw [ite_eq_left hb, ite_eq_left hb]
    refine ⟨Number.operator_neg_isNormalized n hn, ?_, Number.operator_neg_mantissa_of_ne n hm, ?_, ?_⟩
    · rw [Number.operator_neg_negative_of_ne n hm, hb]; rfl
    · unfold Number.operator_neg
      rw [ite_eq_right (by simpa using hm)]
    · rw [Number.toRat_neg]; ring
  · rw [ite_eq_right hb, ite_eq_right hb, one_mul]
    exact ⟨hn, by simpa using hb, rfl, rfl, rfl⟩

/-- An XRP or MPT `ofNumber` result is the `to_rep` integer of the Number without its sign, with the sign put
back. -/
lemma STAmount.ofNumber_integral_signed (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hnt : nt.isIntegral = true) (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    ∃ (w : Number) (iv : Int64), w.isNormalized ∧ w.negative_ = false ∧ w.to_rep mode = .ok iv ∧
      0 ≤ iv.toInt ∧
      n.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) * w.toRat ∧
      result.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) * (iv.toInt : ℚ) ∧
      result.mOffset = 0 := by
  obtain ⟨hw_norm, hw_neg, -, -, hw_val⟩ := STAmount.ofNumber_working_facts n hn
  unfold STAmount.ofNumber at hok
  rw [ite_eq_left hnt] at hok
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  cases hrep : w.to_rep mode with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok iv =>
    rw [hrep] at hok
    simp only [] at hok
    obtain ⟨v, hv, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hv
    rw [STAmount.checked] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range w mode iv hw_neg hrep
    have hint : (STAmount.unchecked nt iv.toUInt64 0 (decide (n.signum < 0))).integral = true := hnt
    have hexact := STAmount.canonicalize_integral_toRat _ result mode hint rfl
      (toUInt64_toNat_le_maxRep iv hnn hle) hok
    have hoff := (STAmount.canonicalize_integral_canonical _ result mode hint hok).1.offset_zero
    refine ⟨w, iv, hw_norm, hw_neg, hrep, hnn, hw_val, ?_, hoff⟩
    rw [hexact, STAmount.toRat_signed]
    show (if decide (n.signum < 0) = true then (-1 : ℚ) else 1) * (iv.toUInt64.toNat : ℚ) * 10 ^ (0 : ℤ) = _
    have hcast : (iv.toUInt64.toNat : ℚ) = (iv.toInt : ℚ) := by
      exact_mod_cast toUInt64_toNat_of_nonneg iv hnn
    rw [Number.signum_neg_decide, zpow_zero, mul_one, hcast]

/-- A nonzero IOU `ofNumber` result is the 16-digit rounding of the Number without its sign, with the sign put
back. -/
lemma STAmount.ofNumber_iou_signed (n : Number) (mode : rounding_mode) (result : STAmount)
    (hn : n.isNormalized) (hn0 : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber .fractional n mode = .ok result) (hresult : result.mValue ≠ 0) :
    ∃ (w : Number) (mant : Int64) (exp : ℤ),
      w.negative_ = false ∧ 10 ^ 18 ≤ w.mantissa_.toNat ∧ w.mantissa_.toNat < 10 ^ 19 ∧
      minExponent ≤ w.exponent_ + 3 ∧ w.exponent_ + 4 ≤ maxExponent ∧
      w.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) ∧ 0 ≤ mant.toInt ∧
      n.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) * w.toRat ∧
      result.toRat = (if n.negative_ = true then (-1 : ℚ) else 1) * ((mant.toInt : ℚ) * 10 ^ exp) ∧
      result.mOffset = exp := by
  obtain ⟨-, hw_neg, hw_mant, hw_exp, hw_val⟩ := STAmount.ofNumber_working_facts n hn
  have hb := mantissaBounds_nat_of (hn.mantissaBounds hn0)
  have hemin := Number.exponent_ge_min n hn hn0
  have hexp4 := STAmount.ofNumber_iou_success_exp_range n mode result hb.1 hb.2 hemin hok hresult
  unfold STAmount.ofNumber at hok
  rw [ite_eq_right (by decide)] at hok
  set w : Number := if decide (n.signum < 0) = true then n.operator_neg else n with hw
  have hw_lo : 10 ^ 18 ≤ w.mantissa_.toNat := by rw [hw_mant]; exact hb.1
  have hw_hi : w.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hb.2
  cases hnorm : w.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : w.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts w mode mant exp hw_lo hw_hi (by omega) (by omega) hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hw_neg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; exact hmlo
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]
      have h := hmhi
      rw [show cMaxValue.toNat = 10 ^ 16 - 1 from by decide] at h
      omega
    obtain ⟨v, hv, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨-, rfl⟩ := Int64.toUInt64Checked_eq_ok.mp hv
    obtain ⟨-, -, hres_eq⟩ :=
      STAmount.checked_iou_cases .fractional mant.toUInt64 exp (decide (n.signum < 0)) mode rfl
        hmtu_lo hmtu_hi (by omega) hexp_le result hok hresult
    refine ⟨w, mant, exp, hw_neg, hw_lo, hw_hi, by omega, by omega, hnorm', hmant_pos, hw_val, ?_,
      by rw [hres_eq]⟩
    rw [hres_eq, STAmount.toRat_signed]
    show (if decide (n.signum < 0) = true then (-1 : ℚ) else 1) * (mant.toUInt64.toNat : ℚ) * 10 ^ exp = _
    have hcast : (mant.toUInt64.toNat : ℚ) = (mant.toInt : ℚ) := by
      exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos
    rw [Number.signum_neg_decide, hcast, mul_assoc]

/-- A nonzero IOU `ofNumber` result comes from a nonzero Number. -/
lemma STAmount.ofNumber_fractional_source_ne_zero (n : Number) (mode : rounding_mode) (result : STAmount)
    (hn : n.isNormalized) (hok : STAmount.ofNumber .fractional n mode = .ok result)
    (hresult : result.mValue ≠ 0) : n.mantissa_ ≠ 0 := by
  intro hm
  rw [Number.eq_zero_of_mantissa_zero n hn hm, STAmount.ofNumber_fractional_zero, Except.ok.injEq] at hok
  exact hresult (by rw [← hok])

/-- Rounding a 19-digit Number that is not negative down to 16 digits gives a value at or below it, less than
one unit away. -/
lemma normalizeToRange_16_floor_pos_bounds (w : Number) (mant : Int64) (exp : Int) (mode : rounding_mode)
    (hmode : mode = .downward ∨ mode = .towards_zero) (hnf : w.negative_ = false)
    (h_lo : 10 ^ 18 ≤ w.mantissa_.toNat) (h_hi : w.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ w.exponent_ + 3) (he_hi : w.exponent_ + 4 ≤ maxExponent)
    (hok : w.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    (mant.toInt : ℚ) * 10 ^ exp ≤ w.toRat ∧ w.toRat - (mant.toInt : ℚ) * 10 ^ exp < (10 : ℚ) ^ exp := by
  obtain ⟨hval, hexp⟩ := normalizeToRange_16_floor_pos w mant exp mode hmode hnf h_lo h_hi he_lo he_hi hok
  rw [hval, hexp, Number.toRat_of_nonneg w hnf, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
  have hp : (0 : ℚ) < (10 : ℚ) ^ w.exponent_ := zpow_pos (by norm_num) _
  have hdm : (w.mantissa_.toNat : ℚ)
      = 1000 * ((w.mantissa_.toNat / 1000 : ℕ) : ℚ) + ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod w.mantissa_.toNat 1000).symm
  have hr0 : (0 : ℚ) ≤ ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) := Nat.cast_nonneg _
  have hr1 : ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) < 1000 := by
    exact_mod_cast Nat.mod_lt w.mantissa_.toNat (by norm_num)
  rw [hdm]
  generalize ((w.mantissa_.toNat / 1000 : ℕ) : ℚ) = q
  generalize ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) = r at hr0 hr1 ⊢
  generalize (10 : ℚ) ^ w.exponent_ = p at hp ⊢
  norm_num
  constructor <;> nlinarith

/-- Rounding a 19-digit Number that is not negative up to 16 digits gives a value at or above it, less than one
unit away. -/
lemma normalizeToRange_16_ceil_pos_bounds (w : Number) (mant : Int64) (exp : Int)
    (hnf : w.negative_ = false)
    (h_lo : 10 ^ 18 ≤ w.mantissa_.toNat) (h_hi : w.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ w.exponent_ + 3) (he_hi : w.exponent_ + 4 ≤ maxExponent)
    (hok : w.normalizeToRange cMinValue cMaxValue .upward = .ok (mant, exp)) :
    w.toRat ≤ (mant.toInt : ℚ) * 10 ^ exp ∧ (mant.toInt : ℚ) * 10 ^ exp - w.toRat < (10 : ℚ) ^ exp := by
  obtain ⟨hval, hexp⟩ := normalizeToRange_16_ceil_pos w mant exp hnf h_lo h_hi he_lo he_hi hok
  have hle : (10 : ℚ) ^ (w.exponent_ + 3) ≤ (10 : ℚ) ^ exp := zpow_le_zpow_right₀ (by norm_num) hexp
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)] at hle hval
  rw [hval, Number.toRat_of_nonneg w hnf]
  have hp : (0 : ℚ) < (10 : ℚ) ^ w.exponent_ := zpow_pos (by norm_num) _
  have hdm : (w.mantissa_.toNat : ℚ)
      = 1000 * ((w.mantissa_.toNat / 1000 : ℕ) : ℚ) + ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod w.mantissa_.toNat 1000).symm
  have hr1 : ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) < 1000 := by
    exact_mod_cast Nat.mod_lt w.mantissa_.toNat (by norm_num)
  by_cases hrem : w.mantissa_.toNat % 1000 = 0
  · rw [ite_eq_right (by simpa using hrem), Nat.add_zero]
    rw [hrem, Nat.cast_zero, add_zero] at hdm
    rw [hdm]
    generalize ((w.mantissa_.toNat / 1000 : ℕ) : ℚ) = q
    generalize (10 : ℚ) ^ w.exponent_ = p at hp hle ⊢
    generalize (10 : ℚ) ^ exp = u at hle ⊢
    norm_num at hle ⊢
    constructor <;> nlinarith
  · rw [ite_eq_left hrem]
    have hr0 : (0 : ℚ) < ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hrem
    rw [hdm]
    push_cast
    generalize ((w.mantissa_.toNat / 1000 : ℕ) : ℚ) = q
    generalize ((w.mantissa_.toNat % 1000 : ℕ) : ℚ) = r at hr0 hr1 ⊢
    generalize (10 : ℚ) ^ w.exponent_ = p at hp hle ⊢
    generalize (10 : ℚ) ^ exp = u at hle ⊢
    norm_num at hle ⊢
    constructor <;> nlinarith

/-- On a Number that is not negative, `to_rep` towards zero is `to_rep` downward. -/
lemma Number.to_rep_towards_zero_eq_downward (n : Number) (hneg : n.negative_ = false) :
    n.to_rep .towards_zero = n.to_rep .downward := by
  have hround : ∀ g : Guard, g.sbit_ = false → g.round .towards_zero = g.round .downward := by
    intro g h
    unfold Guard.round
    simp [h]
  rw [Number.to_rep_eq_spec, Number.to_rep_eq_spec]
  unfold Number.to_repSpec
  simp only [hneg, Bool.false_eq_true, ↓reduceIte]
  by_cases hz : (n.mantissa == 0) = true
  · simp only [hz, ↓reduceIte]
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  by_cases hoff : n.exponent < 0
  · have hsb : (shiftSpec n.mantissa n.exponent Guard.new).2.sbit_ = false := by
      rw [Number.to_rep_shift_sbit]; rfl
    simp only [hoff, ↓reduceIte]
    simp only [hround _ hsb]
  · simp only [hoff, ↓reduceIte]
    simp only [hround Guard.new rfl]

/-- Proof of `STAmount.ofNumber_rounds_downward`. -/
lemma STAmount.ofNumber_rounds_downward_proof (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hnonneg : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    result.toRat ≤ n.toRat ∧ n.toRat - result.toRat < (10 : ℚ) ^ result.mOffset := by
  have hneg := Number.negative_false_of_nonneg n hn hnonneg
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨w, iv, hw, hwneg, hrep, -, hnv, hrv, hoff⟩ :=
      STAmount.ofNumber_integral_signed _ n .downward result rfl hn hok
    rw [hneg, ite_eq_right Bool.false_ne_true, one_mul] at hnv hrv
    obtain ⟨h1, h2⟩ := Number.to_rep_downward_floor w iv hw hwneg hrep
    rw [hoff, zpow_zero, hnv, hrv]
    exact ⟨h1, by linarith⟩
  | fractional =>
    have hresult := hne.resolve_left (by decide)
    have hn0 := STAmount.ofNumber_fractional_source_ne_zero n .downward result hn hok hresult
    obtain ⟨w, mant, exp, hwneg, hlo, hhi, helo, hehi, hnorm, -, hnv, hrv, hoff⟩ :=
      STAmount.ofNumber_iou_signed n .downward result hn hn0 hok hresult
    rw [hneg, ite_eq_right Bool.false_ne_true, one_mul] at hnv hrv
    rw [hoff, hnv, hrv]
    exact normalizeToRange_16_floor_pos_bounds w mant exp .downward (Or.inl rfl) hwneg hlo hhi helo hehi hnorm

/-- Proof of `STAmount.ofNumber_rounds_upward`. -/
lemma STAmount.ofNumber_rounds_upward_proof (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (hnonneg : 0 ≤ n.toRat)
    (hok : STAmount.ofNumber nt n .upward = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    n.toRat ≤ result.toRat ∧ result.toRat - n.toRat < (10 : ℚ) ^ result.mOffset := by
  have hneg := Number.negative_false_of_nonneg n hn hnonneg
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨w, iv, hw, hwneg, hrep, -, hnv, hrv, hoff⟩ :=
      STAmount.ofNumber_integral_signed _ n .upward result rfl hn hok
    rw [hneg, ite_eq_right Bool.false_ne_true, one_mul] at hnv hrv
    obtain ⟨h1, h2⟩ := Number.to_rep_upward_ceil w iv hw hwneg hrep
    rw [hoff, zpow_zero, hnv, hrv]
    exact ⟨h1, by linarith⟩
  | fractional =>
    have hresult := hne.resolve_left (by decide)
    have hn0 := STAmount.ofNumber_fractional_source_ne_zero n .upward result hn hok hresult
    obtain ⟨w, mant, exp, hwneg, hlo, hhi, helo, hehi, hnorm, -, hnv, hrv, hoff⟩ :=
      STAmount.ofNumber_iou_signed n .upward result hn hn0 hok hresult
    rw [hneg, ite_eq_right Bool.false_ne_true, one_mul] at hnv hrv
    rw [hoff, hnv, hrv]
    exact normalizeToRange_16_ceil_pos_bounds w mant exp hwneg hlo hhi helo hehi hnorm

/-- A sign of `-1` or `1` drops out of an absolute value. -/
private lemma abs_sign_mul (b : Bool) (x : ℚ) : |(if b = true then (-1 : ℚ) else 1) * x| = |x| := by
  cases b <;> simp

/-- Proof of `STAmount.ofNumber_rounds_towards_zero`. -/
lemma STAmount.ofNumber_rounds_towards_zero_proof (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n .towards_zero = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    |result.toRat| ≤ |n.toRat| ∧ |n.toRat| - |result.toRat| < (10 : ℚ) ^ result.mOffset := by
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨w, iv, hw, hwneg, hrep, hiv, hnv, hrv, hoff⟩ :=
      STAmount.ofNumber_integral_signed _ n .towards_zero result rfl hn hok
    rw [Number.to_rep_towards_zero_eq_downward w hwneg] at hrep
    obtain ⟨h1, h2⟩ := Number.to_rep_downward_floor w iv hw hwneg hrep
    have hw0 := Number.toRat_nonneg_of_nonnegative w hwneg
    have hiv0 : (0 : ℚ) ≤ (iv.toInt : ℚ) := by exact_mod_cast hiv
    rw [hoff, zpow_zero, hnv, hrv, abs_sign_mul, abs_sign_mul, abs_of_nonneg hw0, abs_of_nonneg hiv0]
    exact ⟨h1, by linarith⟩
  | fractional =>
    have hresult := hne.resolve_left (by decide)
    have hn0 := STAmount.ofNumber_fractional_source_ne_zero n .towards_zero result hn hok hresult
    obtain ⟨w, mant, exp, hwneg, hlo, hhi, helo, hehi, hnorm, hmant, hnv, hrv, hoff⟩ :=
      STAmount.ofNumber_iou_signed n .towards_zero result hn hn0 hok hresult
    have hw0 := Number.toRat_nonneg_of_nonnegative w hwneg
    have hm0 : (0 : ℚ) ≤ (mant.toInt : ℚ) * 10 ^ exp :=
      mul_nonneg (by exact_mod_cast hmant) (zpow_nonneg (by norm_num) _)
    rw [hoff, hnv, hrv, abs_sign_mul, abs_sign_mul, abs_of_nonneg hw0, abs_of_nonneg hm0]
    exact normalizeToRange_16_floor_pos_bounds w mant exp .towards_zero (Or.inr rfl) hwneg hlo hhi helo hehi
      hnorm

/-- Proof of `STAmount.ofNumber_rounds_to_nearest`. -/
lemma STAmount.ofNumber_rounds_to_nearest_proof (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n .to_nearest = .ok result) (hne : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    |result.toRat - n.toRat| ≤ (10 : ℚ) ^ result.mOffset / 2 := by
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨w, iv, hw, hwneg, hrep, -, hnv, hrv, hoff⟩ :=
      STAmount.ofNumber_integral_signed _ n .to_nearest result rfl hn hok
    have h := Number.to_rep_to_nearest_within_half w iv hw hwneg hrep
    rw [hoff, zpow_zero, hnv, hrv, ← mul_sub, abs_sign_mul]
    exact h
  | fractional =>
    have hresult := hne.resolve_left (by decide)
    have hn0 := STAmount.ofNumber_fractional_source_ne_zero n .to_nearest result hn hok hresult
    have h := STAmount.ofNumber_iou_to_nearest_within_half n result hn hn0 hok hresult
    rw [show result.exponent = result.mOffset from rfl] at h
    linarith

/-- The witness of the wrong direction, -1.5, is a normalized Number. -/
lemma STAmount.ofNumber_negative_witness_normalized :
    (⟨true, 1500000000000000000, -18⟩ : Number).isNormalized := by
  decide

/-- `downward` conversion of -1.5 XRP gives -1. -/
lemma STAmount.ofNumber_downward_negative_witness :
    STAmount.ofNumber NumericType.native ⟨true, 1500000000000000000, -18⟩ .downward
      = .ok ⟨NumericType.native, 1, 0, true⟩ := by
  decide +kernel

/-- `upward` conversion of -1.5 XRP gives -2. -/
lemma STAmount.ofNumber_upward_negative_witness :
    STAmount.ofNumber NumericType.native ⟨true, 1500000000000000000, -18⟩ .upward
      = .ok ⟨NumericType.native, 2, 0, true⟩ := by
  decide +kernel

/-- -1.5 is below -1. -/
lemma STAmount.ofNumber_downward_negative_witness_lt :
    (⟨true, 1500000000000000000, -18⟩ : Number).toRat
      < (⟨NumericType.native, 1, 0, true⟩ : STAmount).toRat := by
  decide +kernel

/-- -2 is below -1.5. -/
lemma STAmount.ofNumber_upward_negative_witness_lt :
    (⟨NumericType.native, 2, 0, true⟩ : STAmount).toRat
      < (⟨true, 1500000000000000000, -18⟩ : Number).toRat := by
  decide +kernel

end XRPL.Model.Protocol
