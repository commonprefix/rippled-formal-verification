import XRPL.Properties.Lending.Loan.Common.Grid
import XRPL.Properties.Lending.Loan.Common.SetValue
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Sum
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts

/-! # Rounding to a fractional amount at a scale

A value below 0.49 units rounds to nearest at zero, a value at most zero rounds to at most zero, rounding up never
lowers a value unless it lands on zero, and a nonnegative value never rounds past its next grid point. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- Rounding a small IOU amount to nearest at a coarser exponent gives zero. An amount below `0.499`
units of `10^s` rounds to zero. -/
lemma STAmount.roundToExponent_to_nearest_small (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hneg : value.mIsNegative = false) (hs : -96 ≤ s ∧ s ≤ 80)
    (hsmall : value.toRat < 499 / 1000 * 10 ^ s)
    (hok : STAmount.roundToExponent value s .to_nearest = .ok result) : result.toRat = 0 := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0
    have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo
    omega
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hval := STAmount.toRat_of_nonneg value hneg
  have hmlo : ((10 ^ 15 : ℕ) : ℚ) ≤ (value.mValue.toNat : ℚ) := by exact_mod_cast hc.mant_lo
  have h_ev : value.mOffset < s := by
    by_contra hge
    push Not at hge
    have h1 : (10 : ℚ) ^ s ≤ (10 : ℚ) ^ value.mOffset := zpow_le_zpow_right₀ (by norm_num) hge
    have h2 : (10 : ℚ) ^ value.mOffset ≤ value.toRat := by
      rw [hval]
      have : (1 : ℚ) ≤ (value.mValue.toNat : ℚ) := by
        have : ((10 ^ 15 : ℕ) : ℚ) ≥ 1 := by norm_num
        linarith
      nlinarith [zpow_pos (show (0 : ℚ) < 10 by norm_num) value.mOffset]
    linarith
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true),
      if_neg (by
        show ¬ value.isZero = true
        unfold STAmount.isZero
        rw [beq_eq_false_iff_ne.mpr h_mv_ne]
        exact Bool.false_ne_true),
      if_neg (by show ¬ value.mOffset ≥ s; omega)] at hok
  rw [show STAmount.checked value.mNumericType kMinValue s value.negative .to_nearest
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ from by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative .to_nearest hs.1 hs.2] at hok
  simp only [] at hok
  set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
  obtain ⟨sum, h_sum_ok, h_sub_ok⟩ : ∃ sum,
      STAmount.operator_add value refA .to_nearest = .ok sum ∧
      STAmount.operator_sub sum refA .to_nearest = .ok result := by
    match h1 : STAmount.operator_add value refA .to_nearest with
    | .error e => rw [h1] at hok; exact absurd hok (by intro h; cases h)
    | .ok sum =>
      rw [h1] at hok
      exact ⟨sum, rfl, hok⟩
  obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, h_tn, -, -, -⟩ :=
    STAmount.roundToExponent_sum_spec value s .to_nearest hc h_ev hs.1 hs.2 sum h_sum_ok
  have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
  have hc_ref : refA.IOUCanonical :=
    { is_fractional := hc.is_fractional
      mant_lo := by show 10 ^ 15 ≤ kMinValue.toNat; omega
      mant_hi := by show kMinValue.toNat < 10 ^ 16; omega
      exp_lo := hs.1
      exp_hi := hs.2 }
  have href_val : refA.toRat = (10 : ℚ) ^ 15 * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg refA hneg]
    show (kMinValue.toNat : ℚ) * 10 ^ s = _
    rw [h_kMin_toNat]; push_cast; ring
  have hsum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
    rw [STAmount.toRat_of_nonneg sum (by rw [h_sum_neg]; exact hneg), h_sum_mv, h_sum_off]
  have hsum_ne : sum.mValue ≠ 0 := by
    intro h0
    have : sum.mValue.toNat = 0 := by rw [h0]; rfl
    omega
  have hv0 : 0 < value.toRat := by
    rw [hval]
    have : (0 : ℚ) < (value.mValue.toNat : ℚ) := by
      have : ((10 ^ 15 : ℕ) : ℚ) > 0 := by norm_num
      linarith
    exact mul_pos this (zpow_pos (by norm_num) _)
  have herr := STAmount.operator_add_iou_rel_error value refA sum hc hc_ref
    (by rw [href_val]; exact ne_of_gt (by positivity)) h_sum_ok hsum_ne
  -- the sum is the reference: a step up would be more than half a unit away
  have hk0 : k = 0 := by
    by_contra hk
    have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hpos : 0 < value.toRat + refA.toRat := by rw [href_val]; positivity
    have hdiff : sum.toRat - (value.toRat + refA.toRat) = (k : ℚ) * 10 ^ s - value.toRat := by
      rw [hsum_val, href_val]; push_cast; ring
    rw [hdiff, abs_of_pos hpos] at herr
    have hδ : (6 / (2 ^ 63 - 3 : ℚ) + (1 / 2) * (10 : ℚ) ^ (-15 : ℤ)
        + 6 / (2 ^ 63 - 3 : ℚ) * ((1 / 2) * (10 : ℚ) ^ (-15 : ℤ))) ≤ 5007 / 10 ^ 19 := by
      norm_num
    have hbig : value.toRat + refA.toRat ≤ (10 ^ 15 + 1) * 10 ^ s := by rw [href_val]; linarith
    have h3 := mul_le_mul hbig hδ (by positivity) (by positivity)
    have hle := le_trans (le_abs_self _) herr
    nlinarith
  have hsum_eq : sum = refA := by
    obtain ⟨nt, mv, off, ng⟩ := sum
    simp only at h_sum_asset h_sum_mv h_sum_off h_sum_neg
    have hmv : mv = kMinValue := UInt64.toNat_inj.mp (by rw [h_sum_mv, hk0, h_kMin_toNat]; rfl)
    rw [hrefA_def, h_sum_asset, h_sum_off, h_sum_neg, hmv]
  rw [hsum_eq] at h_sub_ok
  exact STAmount.toRat_eq_zero_of_mValue_zero result
    (STAmount.operator_sub_self_zero refA result .to_nearest hc_ref h_sub_ok)

/-- Rounding a small fractional value to nearest at a scale gives zero. A value below `0.49` units of
`10^s` rounds to zero. -/
lemma STAmount.roundToNumericType_to_nearest_small (x T : Number) (s : ℤ) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80) (hsmall : x.toRat < 49 / 100 * 10 ^ s)
    (hok : STAmount.roundToNumericType .fractional x .to_nearest (some s) = .ok T) : T.toRat = 0 := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber .fractional x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    by_cases hst : st.mValue = 0
    · rw [hof] at hok
      exact STAmount.roundToNumericType_frac_of_zero x T .to_nearest s st hof hst (by
        unfold STAmount.roundToNumericType; rw [hof]; exact hok)
    rw [hof] at hok
    simp only at hok
    have hty := STAmount.ofNumber_mNumericType _ _ _ st hof
    have hint : st.integral = false := by unfold STAmount.integral; rw [hty]; rfl
    rw [if_neg (by rw [hint]; decide)] at hok
    obtain ⟨hc, -, -, -, -⟩ := STAmount.ofNumber_frac_stage x .to_nearest st hx h0 (Or.inl rfl) hof hst
    have hneg := Number.negative_false_of_nonneg x hx h0
    have hst0 : 0 ≤ st.toRat := STAmount.ofNumber_nonneg _ _ _ _ hx hneg hof
    have hsneg := STAmount.mIsNegative_false_of_nonneg st hst0 hst
    -- the 16-digit amount is within half a unit of its last digit, so still below `0.499` units
    have hhalf := STAmount.ofNumber_to_nearest_within_half .fractional x st hx h0 hof hst
    have hstv := STAmount.toRat_of_nonneg st hsneg
    have hmlo : ((10 ^ 15 : ℕ) : ℚ) ≤ (st.mValue.toNat : ℚ) := by exact_mod_cast hc.mant_lo
    have hulp : (10 : ℚ) ^ st.exponent * 10 ^ 15 ≤ st.toRat := by
      rw [hstv]
      have : (0 : ℚ) < 10 ^ st.mOffset := zpow_pos (by norm_num) _
      show (10 : ℚ) ^ st.mOffset * 10 ^ 15 ≤ _
      push_cast at hmlo
      nlinarith
    have hlt : st.toRat < 499 / 1000 * 10 ^ s := by
      have h1 := (abs_le.mp hhalf).2
      nlinarith
    cases hr : STAmount.roundToExponent st s .to_nearest with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only at hok
      have hr0 := STAmount.roundToExponent_to_nearest_small st r s hc hsneg
        ⟨by have := hs.1; omega, hs.2⟩ hlt hr
      by_cases hes : s ≤ st.exponent
      · -- an amount at the scale is at least a unit, too large
        have : (10 : ℚ) ^ s * 10 ^ 15 ≤ st.toRat :=
          le_trans (mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ (by norm_num) hes) (by positivity)) hulp
        nlinarith
      push Not at hes
      obtain ⟨k, -, hrty, hrc, -, -, -⟩ :=
        STAmount.roundToExponent_nonneg_units st r s .to_nearest hc hsneg hes hs.1 hs.2 hr
      rcases hrc with hrz | hrc
      · have hrint : r.integral = false := by unfold STAmount.integral; rw [hrty]; rfl
        rw [STAmount.toNumber_zero_fractional r .to_nearest hrint hrz, Except.ok.injEq] at hok
        rw [← hok, Number.toRat_zero]
      · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r .to_nearest hrc
        rw [hsn, Except.ok.injEq] at hok
        rw [← hok, hv, hr0]

/-- A fractional `ofNumber` of a value at most zero is at most zero. -/
private lemma STAmount.ofNumber_frac_nonpos (x : Number) (mode : rounding_mode) (st : STAmount)
    (hx : x.isNormalized) (h0 : x.toRat ≤ 0) (hof : STAmount.ofNumber .fractional x mode = .ok st) :
    st.toRat ≤ 0 := by
  by_cases hz : x.toRat = 0
  · have hx0 : x = Number.zero := (Number.toRat_eq_zero_iff_eq_zero hx).mp hz
    rw [hx0, STAmount.ofNumber_fractional_zero, Except.ok.injEq] at hof
    rw [← hof, STAmount.toRat_eq_zero_of_mValue_zero _ rfl]
  · have hneg : x.negative_ = true := by
      by_contra hc
      have := Number.toRat_nonneg_of_nonnegative x (by simpa using hc)
      exact hz (le_antisymm h0 this)
    exact STAmount.ofNumber_signtrue_nonpos .fractional x mode st rfl hx hneg hof

/-- Rounding a value at most zero to a fractional amount at a scale gives at most zero. -/
lemma STAmount.roundToNumericType_frac_nonpos (x T : Number) (mode : rounding_mode) (s : ℤ)
    (hx : x.isNormalized) (h0 : x.toRat ≤ 0) (hs : -81 ≤ s ∧ s ≤ 80)
    (hok : STAmount.roundToNumericType .fractional x mode (some s) = .ok T) : T.toRat ≤ 0 := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber .fractional x mode with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    have hfc := STAmount.ofNumber_fractional_fczr x mode st hof
    have hsti : st.integral = false := by unfold STAmount.integral; rw [hfc.1]; rfl
    rw [if_neg (by rw [hsti]; decide)] at hok
    have hst0 := STAmount.ofNumber_frac_nonpos x mode st hx h0 hof
    cases hr : STAmount.roundToExponent st s mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only at hok
      have hrc := STAmount.roundToExponent_fczr st r s mode hfc hr
      have hrint : r.integral = false := by unfold STAmount.integral; rw [hrc.1]; rfl
      have hr0 : r.toRat ≤ 0 := by
        rcases hfc.2 with hstc | hstz
        · have hR := STAmount.roundToExponent_rounded_of_scale st r s mode hstc hs.1 hs.2 hr
          have hq : st.toRat / 10 ^ s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hst0 hp.le
          have hf : (⌊st.toRat / 10 ^ s⌋ : ℚ) ≤ 0 := by exact_mod_cast Int.floor_nonpos hq
          have hc : (⌈st.toRat / 10 ^ s⌉ : ℚ) ≤ 0 := by exact_mod_cast Int.ceil_le.mpr (by simpa using hq)
          unfold RoundsToRepresentableAt at hR
          cases mode with
          | to_nearest =>
            rcases hR with h | h
            · rw [show r.toRat = _ from h]; exact mul_nonpos_of_nonpos_of_nonneg hf hp.le
            · rw [show r.toRat = _ from h]; exact mul_nonpos_of_nonpos_of_nonneg hc hp.le
          | upward => rw [show r.toRat = _ from hR]; exact mul_nonpos_of_nonpos_of_nonneg hc hp.le
          | downward => rw [show r.toRat = _ from hR]; exact mul_nonpos_of_nonpos_of_nonneg hf hp.le
          | towards_zero =>
            rw [show r.toRat = _ from hR]
            split
            · exact mul_nonpos_of_nonpos_of_nonneg hf hp.le
            · exact mul_nonpos_of_nonpos_of_nonneg hc hp.le
        · have hz : st.isZero = true := by unfold STAmount.isZero; simp [hstz]
          rw [STAmount.roundToExponent_eq_self st s mode (Or.inr (Or.inl hz)), Except.ok.injEq] at hr
          rw [← hr]; exact hst0
      rcases hrc.2 with hrcan | hrz
      · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r mode hrcan
        rw [hsn, Except.ok.injEq] at hok
        rw [← hok, hv]; exact hr0
      · rw [STAmount.toNumber_zero_fractional r mode hrint hrz, Except.ok.injEq] at hok
        rw [← hok, Number.toRat_zero]

/-- Rounding up to a fractional amount at a scale never lowers a value, unless it lands on zero. -/
lemma STAmount.roundToNumericType_frac_upward_ge (x T : Number) (s : ℤ) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80) (hT : T.toRat ≠ 0)
    (hok : STAmount.roundToNumericType .fractional x .upward (some s) = .ok T) : x.toRat ≤ T.toRat := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber .fractional x .upward with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    have hfc := STAmount.ofNumber_fractional_fczr x .upward st hof
    have hsti : st.integral = false := by unfold STAmount.integral; rw [hfc.1]; rfl
    rw [if_neg (by rw [hsti]; decide)] at hok
    cases hr : STAmount.roundToExponent st s .upward with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only at hok
      have hrc := STAmount.roundToExponent_fczr st r s .upward hfc hr
      have hrint : r.integral = false := by unfold STAmount.integral; rw [hrc.1]; rfl
      have hTr : T.toRat = r.toRat := by
        rcases hrc.2 with hrcan | hrz
        · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r .upward hrcan
          rw [hsn, Except.ok.injEq] at hok
          rw [← hok, hv]
        · rw [STAmount.toNumber_zero_fractional r .upward hrint hrz, Except.ok.injEq] at hok
          rw [← hok, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hrz]
      rcases hfc.2 with hstc | hstz
      · have hst : st.mValue ≠ 0 := by intro h; have := hstc.mant_lo; rw [h] at this; simp at this
        obtain ⟨-, -, -, hup, -⟩ := STAmount.ofNumber_frac_stage x .upward st hx h0 (Or.inr (Or.inl rfl)) hof hst
        have hR := STAmount.roundToExponent_rounded_of_scale st r s .upward hstc hs.1 hs.2 hr
        unfold RoundsToRepresentableAt at hR
        have hce : st.toRat / 10 ^ s ≤ (⌈st.toRat / 10 ^ s⌉ : ℚ) := Int.le_ceil _
        have : st.toRat ≤ r.toRat := by
          rw [show r.toRat = _ from hR]
          calc st.toRat = st.toRat / 10 ^ s * 10 ^ s := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_right hce hp.le
        rw [hTr]; linarith [hup rfl]
      · have hz : st.isZero = true := by unfold STAmount.isZero; simp [hstz]
        rw [STAmount.roundToExponent_eq_self st s .upward (Or.inr (Or.inl hz)), Except.ok.injEq] at hr
        exact absurd (by rw [hTr, ← hr, STAmount.toRat_eq_zero_of_mValue_zero st hstz]) hT

/-- A nonnegative value rounded to a fractional amount at a scale is at most its next grid point, when the
value is below `10^16 - 1` units. -/
lemma STAmount.roundToNumericType_frac_le_ceil (x T : Number) (mode : rounding_mode) (s : ℤ)
    (hx : x.isNormalized) (h0 : 0 ≤ x.toRat)
    (hmode : mode = .to_nearest ∨ mode = .upward ∨ mode = .downward) (hs : -81 ≤ s ∧ s ≤ 80)
    (hlt : x.toRat < ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ s)
    (hok : STAmount.roundToNumericType .fractional x mode (some s) = .ok T) :
    T.toRat ≤ (⌈x.toRat / 10 ^ s⌉ : ℚ) * 10 ^ s := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hexp : ∀ st, STAmount.ofNumber .fractional x mode = .ok st → st.mValue ≠ 0 → st.exponent ≤ s := by
    intro st hof hst
    obtain ⟨hc, hle, hgf, -, -⟩ := STAmount.ofNumber_frac_stage x mode st hx h0 hmode hof hst
    by_contra hgt
    push Not at hgt
    have hneg := Number.negative_false_of_nonneg x hx h0
    have hst0 : 0 ≤ st.toRat := STAmount.ofNumber_nonneg _ _ _ _ hx hneg hof
    have hsneg := STAmount.mIsNegative_false_of_nonneg st hst0 hst
    have hbig : (10 : ℚ) ^ 16 * 10 ^ s ≤ st.toRat := by
      rw [STAmount.toRat_of_nonneg st hsneg]
      have hm : ((10 ^ 15 : ℕ) : ℚ) ≤ (st.mValue.toNat : ℚ) := by exact_mod_cast hc.mant_lo
      have he : (10 : ℚ) ^ (s + 1) ≤ 10 ^ st.mOffset :=
        zpow_le_zpow_right₀ (by norm_num) (show s + 1 ≤ st.mOffset by exact hgt)
      rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_one] at he
      push_cast at hm
      have : (10 : ℚ) ^ 16 * 10 ^ s = 10 ^ 15 * (10 ^ s * 10) := by ring
      rw [this]
      exact mul_le_mul hm he (by positivity) (by positivity)
    by_cases hxe : x.exponent_ + 3 ≤ s
    · -- `10^16 - 1` units is a grid point of the 16-digit stage, so the stage stays below it
      set d : ℕ := (s - (x.exponent_ + 3)).toNat with hd
      have hdz : ((d : ℤ)) = s - (x.exponent_ + 3) := Int.toNat_of_nonneg (by omega)
      have hgp : (((10 ^ 16 - 1) * 10 ^ d : ℕ) : ℚ) * 10 ^ (x.exponent_ + 3) =
          ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ s := by
        push_cast
        rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), hdz]
        congr 2; ring
      have := hgf.upper ((10 ^ 16 - 1) * 10 ^ d) (by rw [hgp]; exact hlt.le)
      rw [hgp] at this
      have h16 : ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ s < (10 : ℚ) ^ 16 * 10 ^ s := by
        have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
        push_cast; nlinarith
      linarith
    · -- a source this coarse is already at least `10^16` units
      have hm0 : x.mantissa_ ≠ 0 := by
        intro hm
        rw [Number.eq_zero_of_mantissa_zero x hx hm, STAmount.ofNumber_fractional_zero, Except.ok.injEq] at hof
        exact hst (by rw [← hof])
      have hmb := hx.mantissaBounds_nat hm0
      have hxv := Number.toRat_of_nonneg x hneg
      have he : (10 : ℚ) ^ (s - 2) ≤ 10 ^ x.exponent_ := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hm : ((10 ^ 18 : ℕ) : ℚ) ≤ (x.mantissa_.toNat : ℚ) := by exact_mod_cast hmb.1
      have hx16 : (10 : ℚ) ^ 16 * 10 ^ s ≤ x.toRat := by
        rw [hxv]
        have : (10 : ℚ) ^ 16 * 10 ^ s = 10 ^ 18 * 10 ^ (s - 2) := by
          rw [zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring
        rw [this]
        push_cast at hm
        exact mul_le_mul hm he (by positivity) (by positivity)
      have h16 : ((10 ^ 16 - 1 : ℕ) : ℚ) * 10 ^ s < (10 : ℚ) ^ 16 * 10 ^ s := by
        have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
        push_cast; nlinarith
      linarith
  obtain ⟨hgf, -, -, -⟩ := STAmount.roundToNumericType_frac_grid x T mode s hx h0 hmode hs hexp hok
  have hz : (0 : ℤ) ≤ ⌈x.toRat / 10 ^ s⌉ := Int.ceil_nonneg (div_nonneg h0 hp.le)
  have hcast : ((⌈x.toRat / 10 ^ s⌉.toNat : ℕ) : ℚ) = (⌈x.toRat / 10 ^ s⌉ : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  have := hgf.upper ⌈x.toRat / 10 ^ s⌉.toNat (by
    rw [hcast]
    calc x.toRat = x.toRat / 10 ^ s * 10 ^ s := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Int.le_ceil _) hp.le)
  rwa [hcast] at this

/-- Rounding down to a fractional amount at a scale never raises a value at least zero. -/
lemma STAmount.roundToNumericType_frac_downward_le (x T : Number) (s : ℤ) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hs : -81 ≤ s ∧ s ≤ 80)
    (hok : STAmount.roundToNumericType .fractional x .downward (some s) = .ok T) : T.toRat ≤ x.toRat := by
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber .fractional x .downward with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok
    simp only at hok
    have hfc := STAmount.ofNumber_fractional_fczr x .downward st hof
    have hsti : st.integral = false := by unfold STAmount.integral; rw [hfc.1]; rfl
    rw [if_neg (by rw [hsti]; decide)] at hok
    cases hr : STAmount.roundToExponent st s .downward with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only at hok
      have hrc := STAmount.roundToExponent_fczr st r s .downward hfc hr
      have hrint : r.integral = false := by unfold STAmount.integral; rw [hrc.1]; rfl
      have hTr : T.toRat = r.toRat := by
        rcases hrc.2 with hrcan | hrz
        · obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact r .downward hrcan
          rw [hsn, Except.ok.injEq] at hok
          rw [← hok, hv]
        · rw [STAmount.toNumber_zero_fractional r .downward hrint hrz, Except.ok.injEq] at hok
          rw [← hok, Number.toRat_zero, STAmount.toRat_eq_zero_of_mValue_zero r hrz]
      rcases hfc.2 with hstc | hstz
      · have hst : st.mValue ≠ 0 := by intro h; have := hstc.mant_lo; rw [h] at this; simp at this
        obtain ⟨-, -, -, -, hdown⟩ :=
          STAmount.ofNumber_frac_stage x .downward st hx h0 (Or.inr (Or.inr rfl)) hof hst
        have hR := STAmount.roundToExponent_rounded_of_scale st r s .downward hstc hs.1 hs.2 hr
        unfold RoundsToRepresentableAt at hR
        have hfl : (⌊st.toRat / 10 ^ s⌋ : ℚ) ≤ st.toRat / 10 ^ s := Int.floor_le _
        have : r.toRat ≤ st.toRat := by
          rw [show r.toRat = _ from hR]
          calc (⌊st.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ st.toRat / 10 ^ s * 10 ^ s :=
                mul_le_mul_of_nonneg_right hfl hp.le
            _ = st.toRat := by field_simp
        rw [hTr]; linarith [hdown rfl]
      · have hz : st.isZero = true := by unfold STAmount.isZero; simp [hstz]
        rw [STAmount.roundToExponent_eq_self st s .downward (Or.inr (Or.inl hz)), Except.ok.injEq] at hr
        rw [hTr, ← hr, STAmount.toRat_eq_zero_of_mValue_zero st hstz]
        exact h0

end XRPL.Model.Lending
