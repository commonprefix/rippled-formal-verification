import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing

/-! # `STAmount` grid and `ofNumber` offset facts

Generic facts about where an `STAmount` value sits on its exponent grid, and which offsets
`ofNumber` can produce. -/

namespace XRPL.Model.Protocol

/-- Signed-integer-times-grid-step form of `STAmount.toRat`. -/
lemma STAmount.exists_int_grid (a : STAmount) :
    ∃ z : ℤ, a.toRat = (z : ℚ) * 10 ^ a.exponent := by
  refine ⟨if a.mIsNegative then -(a.mValue.toNat : ℤ) else (a.mValue.toNat : ℤ), ?_⟩
  rw [STAmount.toRat_signed]
  show _ = _ * (10 : ℚ) ^ a.mOffset
  rcases h : a.mIsNegative with _ | _ <;> simp

/-- Any `STAmount` sits on its own exponent grid: the trivial `.downward` floor
equation at `s = a.exponent`. -/
lemma STAmount.self_grid (a : STAmount) :
    RoundsToRepresentableAt a a.toRat a.exponent .downward := by
  show a.toRat = (⌊a.toRat / 10 ^ a.exponent⌋ : ℚ) * 10 ^ a.exponent
  obtain ⟨z, hval⟩ := STAmount.exists_int_grid a
  have h10 : ((10 : ℚ) ^ a.exponent) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hdiv : a.toRat / 10 ^ a.exponent = (z : ℚ) := by
    rw [hval]; field_simp
  rw [hdiv, Int.floor_intCast, ← hval]

/-- A nonzero `STAmount` is at least one step of its own grid. -/
lemma STAmount.ulp_le_abs_toRat (a : STAmount) (h : a.mValue ≠ 0) :
    (10 : ℚ) ^ a.exponent ≤ |a.toRat| := by
  rw [STAmount.abs_toRat]
  show (10 : ℚ) ^ a.mOffset ≤ _
  have hnat : a.mValue.toNat ≠ 0 := by
    intro h0
    exact h (by rw [← UInt64.toNat_inj] at *; exact h0)
  have h1 : (1 : ℚ) ≤ (a.mValue.toNat : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnat
  nlinarith [zpow_pos (show (0 : ℚ) < 10 by norm_num) a.mOffset]

/-- A nonzero-mantissa `STAmount` has nonzero value. -/
lemma STAmount.toRat_ne_zero (a : STAmount) (h : a.mValue ≠ 0) : a.toRat ≠ 0 := by
  intro h0
  have hle := STAmount.ulp_le_abs_toRat a h
  rw [h0, abs_zero] at hle
  exact absurd hle (not_le.mpr (zpow_pos (by norm_num) _))

/-- `IOUAmount.ofMantissaExp` output exponent: the canonical zero (`-100`) or the
clamped IOU range `[-96, 80]`. -/
lemma IOUAmount.ofMantissaExp_exponent_cases (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hok : IOUAmount.ofMantissaExp m e mode = .ok i) :
    i.exponent_ = -100 ∨ ((-96 : ℤ) ≤ i.exponent_ ∧ i.exponent_ ≤ 80) := by
  unfold IOUAmount.ofMantissaExp IOUAmount.normalize at hok
  by_cases hm : (m == 0) = true
  · rw [if_pos hm] at hok
    rw [← Except.ok.inj hok]
    exact Or.inl rfl
  · rw [if_neg hm] at hok
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error e' => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      cases hfn : IOUAmount.fromNumber v mode with
      | error e' => rw [hfn] at hok; exact absurd hok (by simp)
      | ok r =>
        rw [hfn] at hok
        simp only [] at hok
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hok; exact absurd hok (by simp)
        · rw [if_neg hhi] at hok
          by_cases hlo : r.exponent_ < cMinOffset
          · rw [if_pos hlo] at hok
            rw [← Except.ok.inj hok]
            exact Or.inl rfl
          · rw [if_neg hlo] at hok
            rw [← Except.ok.inj hok]
            right
            have h1 := not_lt.mp hlo
            have h2 := not_lt.mp hhi
            unfold cMinOffset at h1
            unfold cMaxOffset at h2
            omega

/-- `STAmount.canonicalize` on a fractional record: the output offset is the
canonical zero offset (`-100`) or within the clamped IOU range `[-96, 80]`. -/
lemma STAmount.canonicalize_fractional_offset (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional)
    (hok : s.canonicalize mode = .ok result) :
    result.mOffset = -100 ∨ ((-96 : ℤ) ≤ result.mOffset ∧ result.mOffset ≤ 80) := by
  have hint : ¬ s.integral = true := by
    unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
    unfold STAmount.iou; rw [if_neg hint]
  rw [hiou] at hok
  cases hone : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode with
  | error e => rw [hone] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hone] at hok
    simp only [] at hok
    have heq := Except.ok.inj hok
    have hres : result.mOffset = i.exponent_ := by rw [← heq]
    rw [hres]
    exact IOUAmount.ofMantissaExp_exponent_cases _ _ mode i hone

/-- `STAmount.ofNumber` on a fractional asset: the output offset is `-100` (zero)
or within `[-96, 80]`. -/
lemma STAmount.ofNumber_fractional_offset (nt : NumericType) (n : Number) (mode : rounding_mode)
    (a : STAmount) (hnt : nt = .fractional)
    (hok : STAmount.ofNumber nt n mode = .ok a) :
    a.mOffset = -100 ∨ ((-96 : ℤ) ≤ a.mOffset ∧ a.mOffset ≤ 80) := by
  subst hnt
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ NumericType.fractional.isIntegral = true)] at hok
  cases hnr : (if decide (n.signum < 0) = true then n.operator_neg else n).normalizeToRange
      kMinValue kMaxValue mode with
  | error e => rw [hnr] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨m', e'⟩ := me
    rw [hnr] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    exact STAmount.canonicalize_fractional_offset _ a mode rfl hok

/-- The `ofNumber` sign flag is just the operand's sign bit. -/
lemma Number.signum_neg_decide (n : Number) : decide (n.signum < 0) = n.negative_ := by
  unfold Number.signum
  rcases h : n.negative_ with _ | _
  · by_cases hm : (n.mantissa_ != 0) = true <;> simp [hm]
  · simp

/-- `STAmount.canonicalize` on an integral offset-`0` record: the result is a
canonical integral record of the same numeric type. -/
lemma STAmount.canonicalize_integral_canonical (s result : STAmount) (mode : rounding_mode)
    (hint : s.integral = true)
    (hok : s.canonicalize mode = .ok result) :
    result.IntegralCanonical ∧ result.mNumericType = s.mNumericType := by
  rw [STAmount.canonicalize, if_pos hint] at hok
  by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
  · rw [if_pos hz] at hok
    rw [← Except.ok.inj hok]
    exact ⟨⟨hint, rfl, by simp⟩, rfl⟩
  · rw [if_neg hz] at hok
    by_cases hmoff : s.mOffset > s.mNumericType.maxOffset
    · rw [if_pos hmoff] at hok; exact absurd hok (by simp)
    rw [if_neg hmoff] at hok
    simp only [IntAmount.ofNumber] at hok
    cases hr : (Number.unchecked s.mIsNegative s.mValue s.mOffset).to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only [] at hok
      by_cases hrng : r.toInt.natAbs.toUInt64 > s.mNumericType.maxValue
      · rw [if_pos hrng] at hok; exact absurd hok (by simp)
      rw [if_neg hrng] at hok
      rw [← Except.ok.inj hok]
      refine ⟨⟨hint, rfl, ?_⟩, rfl⟩
      show r.toInt.natAbs.toUInt64.toNat ≤ s.mNumericType.maxValue.toNat
      by_contra hcon
      exact hrng (UInt64.lt_iff_toNat_lt.mpr (by omega))

/-- `STAmount.ofNumber` on an integral type: the result is a canonical integral
record of that type. -/
lemma STAmount.ofNumber_integral_canonical (nt : NumericType) (n : Number)
    (mode : rounding_mode) (a : STAmount)
    (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok a) :
    a.IntegralCanonical ∧ a.mNumericType = nt := by
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  cases hrep : (if decide (n.signum < 0) = true then n.operator_neg else n).to_rep mode with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    exact STAmount.canonicalize_integral_canonical _ a mode
      (show (STAmount.unchecked nt intValue.toUInt64 0 (decide (n.signum < 0))).integral = true
        from hnt) hok

end XRPL.Model.Protocol
