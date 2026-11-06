import XRPL.Properties.Protocol.STAmount.Sub.RoundsWithin
import XRPL.Properties.Protocol.STAmount.Sub.Common.Neg
import XRPL.Properties.Protocol.Number.Sub.ZeroShape
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero
import XRPL.Properties.Protocol.STAmount.RoundToScale.RoundToScale
import XRPL.Properties.Vault.Proofs.Support.Integral
import XRPL.Properties.Vault.Proofs.Support.IntegralFacts
import XRPL.Properties.Protocol.Common.Reduction
import XRPL.Properties.Vault.Proofs.Walk

/-! # Grid rounding and the sum clamp

Facts about `STAmount.roundToExponent` and `clampToSumExponent`. The clamp returns the
delta's magnitude: unchanged for an integral amount, and for a fractional one rounded toward
zero onto the grid of the post-sum exponent, which is never finer than the exponent it is
given. -/

namespace XRPL.Model.Protocol

/-- The magnitude the clamp rounds keeps the delta's type, offset and mantissa, and its value
is the delta's absolute value. -/
lemma clamp_magnitude (delta : STAmount) :
    (if delta.negative then delta.operator_neg else delta).mNumericType = delta.mNumericType ∧
    (if delta.negative then delta.operator_neg else delta).mOffset = delta.mOffset ∧
    (if delta.negative then delta.operator_neg else delta).mValue = delta.mValue ∧
    (if delta.negative then delta.operator_neg else delta).toRat = |delta.toRat| := by
  by_cases hn : delta.negative = true
  · rw [if_pos hn]
    obtain ⟨h1, h2, h3⟩ := STAmount.operator_neg_fields delta
    refine ⟨h1, h2, h3, ?_⟩
    have hle : delta.toRat ≤ 0 := by
      rw [STAmount.toRat_of_neg delta hn]
      have : (0 : ℚ) ≤ (delta.mValue.toNat : ℚ) * 10 ^ delta.mOffset := by positivity
      linarith
    rw [STAmount.operator_neg_toRat, abs_of_nonpos hle]
  · rw [if_neg hn]
    refine ⟨rfl, rfl, rfl, ?_⟩
    have hneg : delta.mIsNegative = false := by simpa [STAmount.negative] using hn
    rw [abs_of_nonneg (by rw [STAmount.toRat_of_nonneg delta hneg]; positivity)]

/-- The clamp is inert on an integral amount. An integral delta is already on every grid
coarser than one unit, so the call returns the delta's magnitude unchanged. -/
lemma clampToSumExponent_integral (amount : Number) (amountDelta : STAmount) (exponent : Int)
    (hint : amountDelta.integral = true) :
    clampToSumExponent amount amountDelta exponent =
      .ok (if amountDelta.negative then amountDelta.operator_neg else amountDelta) := by
  simp [clampToSumExponent, hint, pure, Except.pure]

/-- An integral nonnegative delta clamps to itself. -/
lemma clampToSumExponent_integral_nonneg (amount : Number) (a c : STAmount) (exponent : Int)
    (hint : a.integral = true) (hnn : 0 ≤ a.toRat)
    (hcl : clampToSumExponent amount a exponent = .ok c) : c = a := by
  rw [clampToSumExponent_integral amount a exponent hint] at hcl
  rw [← Except.ok.inj hcl]
  by_cases hz : a.mValue = 0
  · have hid : a.operator_neg = a := by unfold STAmount.operator_neg; simp [hz]
    simp [hid]
  · have hsgn : a.mIsNegative = false := by
      by_contra h
      have := STAmount.toRat_neg_of a (by simpa using h) hz
      linarith
    simp [STAmount.negative, hsgn]

/-- On an integral delta the clamp returns the delta's magnitude, so it changes
nothing but the sign bit: type, offset and mantissa all carry through. -/
lemma clampToSumExponent_integral_fields (amount : Number) (s r : STAmount) (exponent : Int)
    (hint : s.integral = true)
    (hok : clampToSumExponent amount s exponent = .ok r) :
    r.mNumericType = s.mNumericType ∧ r.mOffset = s.mOffset ∧ r.mValue = s.mValue := by
  rw [clampToSumExponent_integral amount s exponent hint] at hok
  rw [← Except.ok.inj hok]
  exact ⟨(clamp_magnitude s).1, (clamp_magnitude s).2.1, (clamp_magnitude s).2.2.1⟩

/-- Rounding a nonnegative canonical amount down onto a grid keeps it nonnegative. -/
lemma STAmount.roundToExponent_downward_nonneg (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    0 ≤ result.toRat := by
  by_cases hrv : result.mValue = 0
  · rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
  · have h := STAmount.roundToExponent_rounded value result s .downward hc hs_lo hs_hi hrv hok
    simp only [RoundsToRepresentableAt] at h
    change result.toRat = _ at h
    have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
    rw [h]
    exact mul_nonneg (by exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hnn hp.le)) hp.le

/-- Rounding a nonnegative canonical amount down onto a grid never raises it. -/
lemma STAmount.roundToExponent_downward_le (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    result.toRat ≤ value.toRat := by
  by_cases hrv : result.mValue = 0
  · have hr0 : result.toRat = 0 := by
      rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
    rw [hr0]; exact hnn
  · have h := STAmount.roundToExponent_rounded value result s .downward hc hs_lo hs_hi hrv hok
    simp only [RoundsToRepresentableAt] at h
    change result.toRat = _ at h
    have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
    rw [h]
    calc (⌊value.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s ≤ value.toRat / 10 ^ s * 10 ^ s :=
          mul_le_mul_of_nonneg_right (Int.floor_le _) hp.le
      _ = value.toRat := div_mul_cancel₀ _ hp.ne'

/-- `numberExponent` is never finer than the exponent it is given. -/
lemma numberExponent_ge (n : Number) (exponent : Int) (nt : NumericType) (e : Int)
    (hok : numberExponent n exponent nt = .ok e) : exponent ≤ e := by
  unfold numberExponent at hok
  by_cases hz : n.operator_eq Number.zero = true
  · simp only [hz, if_true, pure, Except.pure, Except.ok.injEq] at hok
    exact le_of_eq hok
  · simp only [hz, Bool.false_eq_true, if_false] at hok
    cases ha : STAmount.ofNumber nt n .downward with
    | error err => rw [ha] at hok; simp [bind, Except.bind, pure, Except.pure] at hok
    | ok a =>
      rw [ha] at hok
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hok
      rw [← hok]; exact le_max_left _ _

/-- `postSumExponent` reduction. It adds the delta to the total and reads the exponent of
the sum, never finer than `exponent`. -/
lemma postSumExponent_reduces (amount amountDelta : Number) (exponent : Int) (nt : NumericType)
    (e : Int) (hps : postSumExponent amount amountDelta exponent nt = .ok e) :
    ∃ sum : Number, amount.operator_add amountDelta .to_nearest = .ok sum ∧
      numberExponent sum exponent nt = .ok e := by
  unfold postSumExponent at hps
  obtain ⟨sum, hsum, hps⟩ := bind_ok_peel _ _ _ hps
  exact ⟨sum, hsum, hps⟩

/-- The post-sum exponent is at least the given exponent and, for an exponent in the IOU offset
range, stays in that range. -/
lemma postSumExponent_range (amount amountDelta : Number) (exponent : Int) (nt : NumericType)
    (e : Int) (hlo : (-96 : Int) ≤ exponent) (hhi : exponent ≤ 80)
    (hps : postSumExponent amount amountDelta exponent nt = .ok e) :
    exponent ≤ e ∧ (-96 : Int) ≤ e ∧ e ≤ 80 := by
  obtain ⟨sum, _, hne⟩ := postSumExponent_reduces amount amountDelta exponent nt e hps
  have hge := numberExponent_ge sum exponent nt e hne
  rcases numberExponent_range sum exponent nt e hne with h | h | h <;> omega

/-- The clamp on a fractional amount prices the delta, reads the post-sum exponent, and
rounds the magnitude toward zero onto that exponent's grid. -/
lemma clampToSumExponent_frac_reduces (amount : Number) (delta result : STAmount) (exponent : Int)
    (hfrac : delta.integral = false)
    (hok : clampToSumExponent amount delta exponent = .ok result) :
    ∃ (deltaNum : Number) (e : Int), delta.toNumber .to_nearest = .ok deltaNum ∧
      postSumExponent amount deltaNum exponent delta.numericType = .ok e ∧
      STAmount.roundToExponent (if delta.negative then delta.operator_neg else delta) e .towards_zero
        = .ok result := by
  simp only [clampToSumExponent, hfrac, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
    Except.pure] at hok
  walk_ok
  -- the walk also splits the magnitude's `if`, so match each branch against it
  all_goals
    refine ⟨_, _, ‹_›, ‹_›, ?_⟩
    split <;> first | assumption | contradiction

/-- The fractional clamp keeps the canonical-or-zero shape. -/
lemma clampToSumExponent_frac_shape (amount : Number) (delta result : STAmount) (exponent : Int)
    (hdc : delta.FracCanonZero) (hok : clampToSumExponent amount delta exponent = .ok result) :
    result.FracCanonZero := by
  have hfrac : delta.integral = false := by unfold STAmount.integral; rw [hdc.1]; rfl
  obtain ⟨_, e, _, _, hround⟩ := clampToSumExponent_frac_reduces amount delta result exponent hfrac hok
  refine STAmount.roundToExponent_fczr _ result e .towards_zero ?_ hround
  split
  · exact STAmount.operator_neg_fczr delta hdc
  · exact hdc

/-- A zero delta clamps to zero. -/
lemma clampToSumExponent_zero (amount : Number) (delta result : STAmount) (exponent : Int)
    (hz : delta.mValue = 0) (hok : clampToSumExponent amount delta exponent = .ok result) :
    result.mValue = 0 := by
  obtain ⟨hnt, -, hval, -⟩ := clamp_magnitude delta
  by_cases hint : delta.integral = true
  · rw [clampToSumExponent_integral amount delta exponent hint] at hok
    rw [← Except.ok.inj hok, hval, hz]
  · have hfrac : delta.integral = false := by simpa using hint
    obtain ⟨_, e, _, _, hround⟩ := clampToSumExponent_frac_reduces amount delta result exponent hfrac hok
    generalize ha : (if delta.negative then delta.operator_neg else delta) = a at hround hval hnt
    have hzA : a.isZero = true := by unfold STAmount.isZero; rw [hval, hz]; rfl
    have hintA : ¬ a.integral = true := by unfold STAmount.integral at hfrac ⊢; rw [hnt, hfrac]; decide
    unfold STAmount.roundToExponent at hround
    rw [if_neg hintA, if_pos hzA] at hround
    rw [← Except.ok.inj hround, hval, hz]

/-- A nonzero fractional clamp is the floor of the magnitude on the post-sum grid. -/
lemma clampToSumExponent_frac_floor (amount : Number) (delta result : STAmount) (exponent : Int)
    (hdc : delta.FracCanonZero) (hlo : (-96 : Int) ≤ exponent) (hhi : exponent ≤ 80)
    (hnz : result.mValue ≠ 0) (hok : clampToSumExponent amount delta exponent = .ok result) :
    ∃ (deltaNum : Number) (e : Int), delta.toNumber .to_nearest = .ok deltaNum ∧
      postSumExponent amount deltaNum exponent delta.numericType = .ok e ∧ exponent ≤ e ∧
      result.toRat = (⌊|delta.toRat| / 10 ^ e⌋ : ℚ) * 10 ^ e := by
  have hfrac : delta.integral = false := by unfold STAmount.integral; rw [hdc.1]; rfl
  obtain ⟨deltaNum, e, hdn, he, hround⟩ :=
    clampToSumExponent_frac_reduces amount delta result exponent hfrac hok
  obtain ⟨hge, he_lo, he_hi⟩ := postSumExponent_range _ _ _ _ _ hlo hhi he
  obtain ⟨hnt, hoff, hval, hrat⟩ := clamp_magnitude delta
  have hac : (if delta.negative then delta.operator_neg else delta).IOUCanonical := by
    rcases hdc.2 with hc | h0
    · exact ⟨by rw [hnt]; exact hc.is_fractional, by rw [hval]; exact hc.mant_lo,
        by rw [hval]; exact hc.mant_hi, by rw [hoff]; exact hc.exp_lo, by rw [hoff]; exact hc.exp_hi⟩
    · exact absurd (clampToSumExponent_zero amount delta result exponent h0 hok) hnz
  have h := STAmount.roundToExponent_rounded _ result e .towards_zero hac he_lo he_hi hnz hround
  have hv : 0 ≤ (if delta.negative then delta.operator_neg else delta).toRat := by
    rw [hrat]; exact abs_nonneg _
  refine ⟨deltaNum, e, hdn, he, hge, ?_⟩
  simp only [RoundsToRepresentableAt] at h
  change result.toRat = _ at h
  rw [h, if_pos hv, hrat]

/-- The fractional clamp never reports a negative amount, nor more than the delta's
magnitude. -/
lemma clampToSumExponent_frac_bounds (amount : Number) (delta result : STAmount) (exponent : Int)
    (hdc : delta.FracCanonZero) (hlo : (-96 : Int) ≤ exponent) (hhi : exponent ≤ 80)
    (hok : clampToSumExponent amount delta exponent = .ok result) :
    0 ≤ result.toRat ∧ result.toRat ≤ |delta.toRat| := by
  by_cases hz : result.mValue = 0
  · have h0 : result.toRat = 0 := by unfold STAmount.toRat; simp [hz]
    rw [h0]; exact ⟨le_refl _, abs_nonneg _⟩
  · obtain ⟨_, e, _, _, _, hfl⟩ := clampToSumExponent_frac_floor amount delta result exponent hdc hlo hhi hz hok
    have hp : (0 : ℚ) < 10 ^ e := zpow_pos (by norm_num) _
    have hq : 0 ≤ |delta.toRat| / 10 ^ e := div_nonneg (abs_nonneg _) hp.le
    rw [hfl]
    constructor
    · exact mul_nonneg (by exact_mod_cast Int.floor_nonneg.mpr hq) hp.le
    · calc (⌊|delta.toRat| / 10 ^ e⌋ : ℚ) * 10 ^ e ≤ |delta.toRat| / 10 ^ e * 10 ^ e :=
            mul_le_mul_of_nonneg_right (Int.floor_le _) hp.le
        _ = |delta.toRat| := div_mul_cancel₀ _ hp.ne'

end XRPL.Model.Protocol
