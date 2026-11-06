import XRPL.Properties.Vault.Proofs.Support.ClampFacts
import XRPL.Properties.Vault.Proofs.Support.STAmountFacts
import XRPL.Properties.Vault.Proofs.Frame
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Vault.Proofs.Support.ComputeDeposit
import XRPL.Properties.Vault.Common.Reduction

/-! # Vault balance updates

The value of the cash a deposit, withdrawal or clawback moves, and the cash update itself. A
canonical-or-zero amount converts to a `Number` of the same value, the clamp keeps that form, and
the update refuses only a negative new cash, which a deposit's nonnegative charge never gives. -/

namespace XRPL.Model.Protocol

/-- A canonical-or-zero amount converts to a `Number` of the same value. -/
lemma STAmount.CanonicalOrZero.toNumber_exact {s : STAmount} (hs : s.CanonicalOrZero) (n : Number)
    (h : s.toNumber .to_nearest = .ok n) : n.toRat = s.toRat ∧ n.isNormalized := by
  rcases hs with hc | hz
  · obtain ⟨sn, hsn, hv, hn⟩ := STAmount.toNumber_canonical_exact s .to_nearest hc
    rw [hsn, Except.ok.injEq] at h
    subst h
    exact ⟨hv, hn⟩
  · exact STAmount.toNumber_zero_facts s .to_nearest n (by simpa [STAmount.isZero] using hz) h

/-- A fractional canonical-or-zero record is canonical-or-zero. -/
lemma STAmount.FracCanonZero.canonicalOrZero {s : STAmount} (h : s.FracCanonZero) : s.CanonicalOrZero := by
  have hfr : s.integral = false := by unfold STAmount.integral; rw [h.1]; rfl
  rcases h.2 with hc | hz
  · exact Or.inl ⟨fun hi => absurd (hi.symm.trans hfr) (by decide), fun _ => hc⟩
  · exact Or.inr (by simp [STAmount.isZero, hz])

/-- An integral record within its type's bound, where that bound fits `maxRep`, is canonical. -/
lemma STAmount.IntegralCanonical.canonical {s : STAmount} (h : s.IntegralCanonical)
    (hmax : s.mNumericType.maxValue.toNat ≤ maxRep.toNat) : s.Canonical :=
  ⟨fun _ => ⟨h, hmax⟩, fun hfr => absurd (h.is_integral.symm.trans hfr) (by decide)⟩

/-- A fractional canonical-or-zero amount is a canonical-or-zero IOU. -/
lemma STAmount.CanonicalOrZero.fracCanonZero {s : STAmount} (hd : s.CanonicalOrZero)
    (hfr : s.integral = false) : s.FracCanonZero := by
  have hnt_fr : s.mNumericType = .fractional := by
    unfold STAmount.integral at hfr
    cases h : s.mNumericType with
    | fractional => rfl
    | integral _ _ _ _ => rw [h] at hfr; simp [NumericType.isIntegral] at hfr
  refine ⟨hnt_fr, ?_⟩
  rcases hd with hc | hz
  · exact Or.inl (hc.2 hfr)
  · exact Or.inr (by simpa [STAmount.isZero] using hz)

/-- The clamp keeps a canonical-or-zero amount canonical-or-zero, of the same type and
nonnegative. -/
lemma clampToSumExponent_canonicalOrZero (amount : Number) (delta result : STAmount) (exponent : Int)
    (hd : delta.CanonicalOrZero) (hlo : (-96 : Int) ≤ exponent) (hhi : exponent ≤ 80)
    (hok : clampToSumExponent amount delta exponent = .ok result) :
    result.CanonicalOrZero ∧ result.mNumericType = delta.mNumericType ∧ 0 ≤ result.toRat := by
  obtain ⟨hnt, hoff, hval, hrat⟩ := clamp_magnitude delta
  by_cases hint : delta.integral = true
  · rw [clampToSumExponent_integral amount delta exponent hint, Except.ok.injEq] at hok
    subst hok
    refine ⟨?_, hnt, by rw [hrat]; exact abs_nonneg _⟩
    rcases hd with hc | hz
    · obtain ⟨hic, hmax⟩ := hc.1 hint
      refine Or.inl (STAmount.IntegralCanonical.canonical
        ⟨by rw [hnt]; exact hic.is_integral, by rw [hoff]; exact hic.offset_zero,
          by rw [hval, hnt]; exact hic.in_range⟩ (by rw [hnt]; exact hmax))
    · exact Or.inr (by unfold STAmount.isZero at hz ⊢; rw [hval]; exact hz)
  · have hdc := hd.fracCanonZero (by simpa using hint)
    have hsh := clampToSumExponent_frac_shape amount delta result exponent hdc hok
    exact ⟨hsh.canonicalOrZero, by rw [hsh.1, hdc.1],
      (clampToSumExponent_frac_bounds amount delta result exponent hdc hlo hhi hok).1⟩

/-- The clamp never grows the amount: the result is at most the magnitude of the delta. -/
lemma clampToSumExponent_le_abs (amount : Number) (delta result : STAmount) (exponent : Int)
    (hd : delta.CanonicalOrZero) (hlo : (-96 : Int) ≤ exponent) (hhi : exponent ≤ 80)
    (hok : clampToSumExponent amount delta exponent = .ok result) :
    result.toRat ≤ |delta.toRat| := by
  obtain ⟨-, -, -, hrat⟩ := clamp_magnitude delta
  by_cases hint : delta.integral = true
  · rw [clampToSumExponent_integral amount delta exponent hint, Except.ok.injEq] at hok
    rw [← hok, hrat]
  · exact (clampToSumExponent_frac_bounds amount delta result exponent (hd.fracCanonZero (by simpa using hint))
      hlo hhi hok).2

/-- The clamp lands on the grid of its exponent: the result is a whole number of units at the
exponent the clamp is called with, never finer. -/
lemma clampToSumExponent_units (amount : Number) (delta result : STAmount) (exponent : Int)
    (hd : delta.CanonicalOrZero) (hlo : (-96 : Int) ≤ exponent) (hhi : exponent ≤ 80)
    (hint : delta.integral = true → exponent ≤ 0)
    (hok : clampToSumExponent amount delta exponent = .ok result) :
    ∃ k : ℕ, result.toRat = (k : ℚ) * (10 : ℚ) ^ exponent := by
  by_cases hz : result.mValue = 0
  · exact ⟨0, by rw [(STAmount.toRat_eq_zero_iff _).mpr hz]; simp⟩
  by_cases hi : delta.integral = true
  · -- an integral clamp is the magnitude, a whole number of units at offset zero
    have he := hint hi
    rw [clampToSumExponent_integral amount delta exponent hi, Except.ok.injEq] at hok
    obtain ⟨-, hoff, hval, hrat⟩ := clamp_magnitude delta
    rw [← hok] at hz
    rw [← hok, hrat]
    have hdz : delta.mValue ≠ 0 := by rw [← hval]; exact hz
    have hc : delta.Canonical := hd.resolve_right (by simpa [STAmount.isZero] using hdz)
    have habs := STAmount.abs_toRat delta
    rw [(hc.1 hi).1.offset_zero, zpow_zero, mul_one] at habs
    refine ⟨delta.mValue.toNat * 10 ^ (-exponent).toNat, ?_⟩
    rw [habs]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num), Int.toNat_of_nonneg (by omega)]
    simp
  · have hdc := hd.fracCanonZero (by simpa using hi)
    obtain ⟨_, e, _, _, hge, hfl⟩ := clampToSumExponent_frac_floor amount delta result exponent hdc hlo hhi hz hok
    have hfl0 : 0 ≤ ⌊|delta.toRat| / 10 ^ e⌋ := Int.floor_nonneg.mpr (by positivity)
    refine ⟨(⌊|delta.toRat| / 10 ^ e⌋).toNat * 10 ^ (e - exponent).toNat, ?_⟩
    have h1 : ((⌊|delta.toRat| / 10 ^ e⌋.toNat : ℕ) : ℚ) = ⌊|delta.toRat| / 10 ^ e⌋ := by
      have := Int.toNat_of_nonneg hfl0
      exact_mod_cast this
    have h2 : (10 : ℚ) ^ (e - exponent).toNat = (10 : ℚ) ^ (e - exponent) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hfl]
    push_cast
    rw [h1, h2, mul_assoc, ← zpow_add₀ (by norm_num)]
    congr 2
    ring

/-- Rounding a nonnegative normalized `Number` to an asset's precision keeps it nonnegative. -/
lemma STAmount.roundToNumericType_nonneg (nt : NumericType) (s r : Number) (hs : s.isNormalized)
    (h0 : 0 ≤ s.toRat) (hok : STAmount.roundToNumericType nt s .to_nearest = .ok r) : 0 ≤ r.toRat := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt s .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok ret =>
    rw [hof] at hok
    have hret : 0 ≤ ret.toRat :=
      STAmount.ofNumber_nonneg nt s .to_nearest ret hs (Number.negative_false_of_nonneg s hs h0) hof
    by_cases hz : ret.mValue = 0
    · rw [(STAmount.toNumber_zero_facts ret .to_nearest r hz hok).1]; exact hret
    · rw [(STAmount.toNumber_exact_of ret r (STAmount.ofNumber_exactCanonical nt s .to_nearest ret hs h0 hof hz)
        hok).1]
      exact hret

/-- `checked` stores a canonical-or-zero amount of its type, given an integral type's bound fits
`maxRep`. -/
lemma STAmount.checked_canonicalOrZero (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (mode : rounding_mode) (result : STAmount)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat)
    (hok : STAmount.checked nt m e neg mode = .ok result) :
    result.CanonicalOrZero ∧ result.mNumericType = nt := by
  rw [STAmount.checked] at hok
  have hty := STAmount.canonicalize_mNumericType _ result mode hok
  refine ⟨?_, hty⟩
  cases hint : nt.isIntegral
  · have hfr := NumericType.eq_fractional_of_not_integral hint
    exact (STAmount.canonicalize_fczr _ result mode hfr hok).canonicalOrZero
  · obtain ⟨hic, -⟩ := STAmount.canonicalize_integral_canonical _ result mode
      (show (STAmount.unchecked nt m e neg).integral = true from hint) hok
    exact Or.inl (hic.canonical (by rw [hty]; exact hmax hint))

/-- `ofNumber` stores a canonical-or-zero amount of its type, given an integral type's bound fits
`maxRep`. -/
lemma STAmount.ofNumber_canonicalOrZero (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    result.CanonicalOrZero ∧ result.mNumericType = nt := by
  have hty := STAmount.ofNumber_mNumericType nt n mode result hok
  refine ⟨?_, hty⟩
  cases hint : nt.isIntegral
  · have hfr := NumericType.eq_fractional_of_not_integral hint
    subst hfr
    exact (STAmount.ofNumber_fractional_fczr n mode result hok).canonicalOrZero
  · obtain ⟨hic, -⟩ := STAmount.ofNumber_integral_canonical nt n mode result hint hok
    exact Or.inl (hic.canonical (by rw [hty]; exact hmax hint))

/-- An integer within half a unit of a value is that value's floor or ceiling. -/
lemma int_floor_or_ceil_of_near (z : ℤ) (x : ℚ) (h : |(z : ℚ) - x| ≤ 1 / 2) :
    (z : ℚ) = ⌊x⌋ ∨ (z : ℚ) = ⌈x⌉ := by
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  by_cases hzx : (z : ℚ) ≤ x
  · left
    have h1 : z ≤ ⌊x⌋ := Int.le_floor.mpr hzx
    have h2 : (⌊x⌋ : ℚ) < z + 1 := by linarith [Int.floor_le x]
    have h2' : ⌊x⌋ < z + 1 := by exact_mod_cast h2
    exact_mod_cast le_antisymm h1 (by omega)
  · right
    push Not at hzx
    have h1 : ⌈x⌉ ≤ z := Int.ceil_le.mpr hzx.le
    have h2 : (z : ℚ) < ⌈x⌉ + 1 := by linarith [Int.le_ceil x]
    have h2' : z < ⌈x⌉ + 1 := by exact_mod_cast h2
    exact_mod_cast le_antisymm (by omega) h1

/-- A `to_nearest` conversion into an asset lands on the floor or the ceiling of its source on the grid of the
result's exponent. A fractional result must be nonzero, since a flush to zero leaves the grid. -/
lemma STAmount.ofNumber_to_nearest_neighbour (nt : NumericType) (n : Number) (result : STAmount)
    (hn : n.isNormalized) (h0 : 0 ≤ n.toRat) (hok : STAmount.ofNumber nt n .to_nearest = .ok result)
    (hnz : nt.isIntegral = true ∨ result.mValue ≠ 0) :
    RoundsToRepresentableAt result n.toRat result.exponent .to_nearest := by
  have hhalf : |result.toRat - n.toRat| ≤ 1 / 2 * (10 : ℚ) ^ result.exponent := by
    rcases hnz with hint | hrz
    · have hoff : result.exponent = 0 :=
        (STAmount.ofNumber_integral_canonical nt n .to_nearest result hint hok).1.offset_zero
      rw [hoff, zpow_zero, mul_one]
      exact STAmount.ofNumber_integral_within_half nt n result hint hn (Number.negative_false_of_nonneg n hn h0) hok
    · exact STAmount.ofNumber_to_nearest_within_half nt n result hn h0 hok hrz
  obtain ⟨z, hz⟩ := STAmount.exists_int_grid result
  have hp : (0 : ℚ) < 10 ^ result.exponent := zpow_pos (by norm_num) _
  have hnear : |(z : ℚ) - n.toRat / 10 ^ result.exponent| ≤ 1 / 2 := by
    have h1 : (z : ℚ) - n.toRat / 10 ^ result.exponent = (result.toRat - n.toRat) / 10 ^ result.exponent := by
      rw [hz]; field_simp
    rw [h1, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact hhalf
  show result.toRat = _ ∨ result.toRat = _
  rcases int_floor_or_ceil_of_near z _ hnear with h | h
  · left; rw [hz, h]
  · right; rw [hz, h]

/-- A fractional conversion of a value of at least `10⁻⁸¹` is never zero. The smallest positive
IOU amount is `10⁻⁸¹`, so only a smaller value can flush to zero. -/
lemma STAmount.ofNumber_frac_ne_zero_of_ge (n : Number) (mode : rounding_mode) (result : STAmount)
    (hn : n.isNormalized) (hge : (10 : ℚ) ^ (-81 : ℤ) ≤ n.toRat)
    (hok : STAmount.ofNumber .fractional n mode = .ok result) : result.mValue ≠ 0 := by
  have h81 : (0 : ℚ) < (10 : ℚ) ^ (-81 : ℤ) := zpow_pos (by norm_num) _
  have hn0 : 0 ≤ n.toRat := by linarith
  have hnm : n.mantissa_ ≠ 0 := fun h0 => by
    rw [Number.toRat_eq_zero_of_mantissa_zero n h0] at hge
    linarith
  -- a value of at least `10⁻⁸¹` has an exponent of at least `-99`
  have hexp : (-99 : ℤ) ≤ n.exponent_ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨-, hm_hi⟩ := hn.mantissaBounds_nat hnm
    have hm : (n.mantissa_.toNat : ℚ) < 10 ^ 19 := by exact_mod_cast hm_hi
    have hp : (10 : ℚ) ^ n.exponent_ ≤ 10 ^ (-100 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hnv : n.toRat < 10 ^ 19 * 10 ^ (-100 : ℤ) := by
      rw [Number.toRat_of_nonneg n (Number.negative_false_of_nonneg n hn hn0)]
      calc (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ (-100 : ℤ) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ < 10 ^ 19 * 10 ^ (-100 : ℤ) := mul_lt_mul_of_pos_right hm (zpow_pos (by norm_num) _)
    have h19 : (10 : ℚ) ^ 19 * 10 ^ (-100 : ℤ) = 10 ^ (-81 : ℤ) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; norm_num
    linarith
  exact STAmount.ofNumber_iou_ne_zero_of_exponent n mode result hn hnm hexp hok

/-- A `Number` that is not negative has a nonnegative sign. -/
lemma Number.signum_nonneg_of_negative_false (n : Number) (h : n.negative_ = false) : 0 ≤ n.signum := by
  unfold Number.signum
  simp only [h, Bool.false_eq_true, if_false]
  split <;> norm_num

/-- A canonical MPT amount is below `2^63` in magnitude. -/
lemma STAmount.IntegralCanonical.abs_le_int64 {s : STAmount} (hs : s.IntegralCanonical)
    (h64 : s.mNumericType = .int64) : |s.toRat| ≤ 2 ^ 63 - 1 := by
  have habs := STAmount.abs_toRat s
  rw [hs.offset_zero, zpow_zero, mul_one] at habs
  have hin := hs.in_range
  rw [h64] at hin
  have : (s.mValue.toNat : ℚ) ≤ 9223372036854775807 := by exact_mod_cast hin
  rw [habs]; linarith

/-- A nonnegative value rounded to an asset is one the asset stores exactly, for an asset whose
integral maximum fits an `int64`. -/
lemma STAmount.isRounded_eq_false_of_rounded (nt : NumericType) (x y : Number)
    (hmax : nt.isIntegral = true → nt.maxValue.toNat ≤ maxRep.toNat)
    (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) (hy0 : 0 ≤ y.toRat) :
    STAmount.isRounded nt y = false := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok ret =>
    rw [hof] at hok
    simp only at hok
    obtain ⟨hcz, hty⟩ := STAmount.ofNumber_canonicalOrZero nt x _ ret hmax hof
    obtain ⟨hyv, hyn⟩ := hcz.toNumber_exact y hok
    by_cases hz : ret.mValue = 0
    · have hy : y.toRat = 0 := by rw [hyv]; unfold STAmount.toRat; simp [hz]
      rw [(Number.toRat_eq_zero_iff_eq_zero hyn).mp hy]
      exact STAmount.isRounded_zero nt
    have hc : ret.Canonical := hcz.resolve_right (by simpa [STAmount.isZero] using hz)
    have hneg : ret.mIsNegative = false := by
      by_contra h
      have := STAmount.toRat_neg_of ret (by simpa using h) hz
      linarith
    have hval : ret.toRat = (ret.mValue.toNat : ℚ) * 10 ^ ret.mOffset := by
      rw [← STAmount.abs_toRat, abs_of_nonneg (STAmount.toRat_nonneg_of ret hneg)]
    rw [STAmount.isRounded_eq_false_iff nt y hyn hy0, hyv, hval]
    refine Or.inr ?_
    cases hnt : nt with
    | integral mv mo ms msh =>
      have hint : nt.isIntegral = true := by rw [hnt]; rfl
      have hrint : ret.integral = true := by unfold STAmount.integral; rw [hty]; exact hint
      obtain ⟨hic, hmx⟩ := hc.1 hrint
      have hmo := STAmount.ofNumber_integral_maxOffset_nonneg nt x .to_nearest ret hint hof hz
      rw [hnt] at hmo hty
      have hin := hic.in_range
      rw [hty] at hin hmx
      refine ⟨hmo, ret.mValue.toNat, hin, by
        have : maxRep.toNat = 9223372036854775807 := rfl
        simp only [NumericType.maxValue] at hin hmx ⊢; omega, ?_⟩
      rw [hic.offset_zero, zpow_zero, mul_one]
    | fractional =>
      have hiou := hc.2 (by unfold STAmount.integral; rw [hty, hnt]; rfl)
      exact ⟨ret.mValue.toNat, ret.mOffset, hiou.mant_lo, hiou.mant_hi, hiou.exp_lo, hiou.exp_hi, rfl⟩

/-- Two whole rationals whose sum lies strictly inside `(-2^63, 2^63)` add to a numerator below `2^63` in
magnitude. -/
lemma Rat.num_natAbs_add_lt_of_den_one (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1)
    (hlo : -2 ^ 63 < a + b) (hhi : a + b < 2 ^ 63) : (a + b).num.natAbs < 2 ^ 63 := by
  have hsumeq : a + b = ((a.num + b.num : ℤ) : ℚ) := by
    rw [Int.cast_add, Rat.coe_int_num_of_den_eq_one ha, Rat.coe_int_num_of_den_eq_one hb]
  rw [hsumeq] at hlo hhi ⊢
  rw [Rat.num_intCast]
  have h1 : -2 ^ 63 < a.num + b.num := by exact_mod_cast hlo
  have h2 : a.num + b.num < 2 ^ 63 := by exact_mod_cast hhi
  omega

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A lawful vault's base exponent is between `-10` and `0`, and `0` for an integral asset. -/
lemma Vault.baseExponent_bounds (v : Vault) :
    (-10 : Int) ≤ v.baseExponent ∧ v.baseExponent ≤ 0 ∧
      (v.numericType.isIntegral = true → v.baseExponent = 0) := by
  have hs : v.scale.toNat ≤ 10 := by
    have := v.wf.scale_le
    rw [UInt8.le_iff_toNat_le] at this
    simpa [vaultMaximumIOUScale] using this
  unfold Vault.baseExponent NumericType.baseExponent
  split <;> simp_all

/-- A lawful vault's base exponent lies inside the IOU offset range. -/
lemma Vault.baseExponent_range (v : Vault) : (-96 : Int) ≤ v.baseExponent ∧ v.baseExponent ≤ 80 :=
  ⟨by have := v.baseExponent_bounds.1; omega, by have := v.baseExponent_bounds.2.1; omega⟩

/-- The cash update refuses only a negative new cash. On a lawful vault every other balance is
nonnegative, so a `tefBAD_LEDGER` from the update means the new `assetsAvailable` would be negative. -/
lemma Vault.adjustAssetsAndShares_bad_ledger (v : Vault) (assets shares : STAmount)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.error .tefBAD_LEDGER)) :
    ∃ assetsNum s aa' : Number, assets.toNumber .to_nearest = .ok assetsNum ∧
      v.assetsAvailable.operator_add assetsNum .to_nearest = .ok s ∧
      STAmount.roundToNumericType v.numericType s .to_nearest = .ok aa' ∧ aa'.signum < 0 := by
  have hnn : ∀ n : Number, n.isNormalized → Number.zero.operator_le n = true → ¬ n.signum < 0 := by
    intro n hn hle
    have h0 : 0 ≤ n.toRat := by
      have := (operator_le_iff _ _ Number.zero_isNormalized hn).mp hle
      rwa [Number.toRat_zero] at this
    exact not_lt.mpr (Number.signum_nonneg_of_negative_false n (Number.negative_false_of_nonneg n hn h0))
  simp only [Vault.adjustAssetsAndShares, Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals
    simp only [Number.operator_add_zero_right, Except.ok.injEq] at *
    subst_vars
  simp only [Bool.or_eq_true, decide_eq_true_eq] at *
  rcases ‹_ ∨ _› with (((h | h) | h) | h) | h
  · exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, h⟩
  · exact absurd h (hnn _ v.wf.assetsDeployed_norm v.valid.assetsDeployed_nonneg)
  · exact absurd h (hnn _ v.wf.lossUnrealized_norm v.valid.lossUnrealized_nonneg)
  · exact absurd h (hnn _ v.wf.yieldUnrealized_norm v.valid.yieldUnrealized_nonneg)
  · exact absurd h (hnn _ v.wf.assetsReserved_norm v.valid.assetsReserved_nonneg)

/-- A cash update that keeps the cash nonnegative never reports `tefBAD_LEDGER`. -/
lemma Vault.adjustAssetsAndShares_not_bad_ledger_of_le (v : Vault) (assets shares : STAmount)
    (hc : assets.CanonicalOrZero) (hle : 0 ≤ v.assetsAvailable.toRat + assets.toRat) :
    (v.adjustAssetsAndShares assets shares).run ≠ .ok (.error .tefBAD_LEDGER) := by
  intro h
  obtain ⟨assetsNum, s, aa', hnum, hs, haa, hneg⟩ := Vault.adjustAssetsAndShares_bad_ledger v assets shares h
  obtain ⟨hv, hnorm⟩ := hc.toNumber_exact assetsNum hnum
  have hsn : s.isNormalized :=
    operator_add_isNormalized_to_nearest_sz _ _ _ v.wf.assetsAvailable_norm hnorm hs
  have hsum : 0 ≤ s.toRat :=
    operator_add_nonneg _ _ _ v.wf.assetsAvailable_norm hnorm hs (by rw [hv]; exact hle)
  have haa0 := STAmount.roundToNumericType_nonneg _ _ _ hsn hsum haa
  have haan := STAmount.roundToNumericType_isNormalized _ _ _ _ _ haa
  exact absurd hneg (not_lt.mpr
    (Number.signum_nonneg_of_negative_false _ (Number.negative_false_of_nonneg _ haan haa0)))

/-- A cash update that adds a nonnegative amount never reports `tefBAD_LEDGER`. -/
lemma Vault.adjustAssetsAndShares_not_bad_ledger (v : Vault) (assets shares : STAmount)
    (hc : assets.CanonicalOrZero) (hnn : 0 ≤ assets.toRat) :
    (v.adjustAssetsAndShares assets shares).run ≠ .ok (.error .tefBAD_LEDGER) := by
  have hAA : 0 ≤ v.assetsAvailable.toRat := v.exact.assetsAvailable_nonneg
  exact Vault.adjustAssetsAndShares_not_bad_ledger_of_le v assets shares hc (by linarith)

/-- On a lawful vault the cash update can only refuse with `tefBAD_LEDGER`. It leaves the loss
and the deployed assets as they are, and `Valid` keeps the loss within them. -/
lemma Vault.adjustAssetsAndShares_rejected_bad_ledger (v : Vault) (assets shares : STAmount) (ter : TER)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.error ter)) : ter = .tefBAD_LEDGER := by
  have hle : v.lossUnrealized.operator_gt v.assetsDeployed = false := by
    have := v.valid.lossUnrealized_le
    unfold Number.operator_le at this
    unfold Number.operator_gt
    simpa using this
  simp only [Vault.adjustAssetsAndShares, Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  all_goals simp only [Number.operator_add_zero_right, Except.ok.injEq] at *
  all_goals subst_vars
  all_goals first | rfl | simp_all

/-- A cash update never reports `tecLIMIT_EXCEEDED`. -/
lemma Vault.adjustAssetsAndShares_not_limit (v : Vault) (assets shares : STAmount) :
    (v.adjustAssetsAndShares assets shares).run ≠ .ok (.error .tecLIMIT_EXCEEDED) := fun h =>
  absurd (Vault.adjustAssetsAndShares_rejected_bad_ledger v assets shares _ h) (by decide)

/-- A canonical deposit amount in the vault's asset bounds an integral asset type within `maxRep`. -/
lemma Vault.maxValue_fits_of_canonical (v : Vault) (a : STAmount) (hc : a.Canonical)
    (hty : a.mNumericType = v.numericType) :
    v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat := by
  intro hint
  have hai : a.integral = true := by unfold STAmount.integral; rw [hty]; exact hint
  have := (hc.1 hai).2
  rwa [hty] at this

/-- The assets a share count is worth at deposit are canonical-or-zero, in the vault's asset. -/
lemma sharesToAssetsDeposit_form (v : Vault) (shares assets : STAmount)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : sharesToAssetsDeposit v shares = .ok assets) :
    assets.CanonicalOrZero ∧ assets.mNumericType = v.numericType := by
  simp only [sharesToAssetsDeposit, bind, Except.bind, pure, Except.pure] at hok
  walk_ok
  all_goals first
    | exact STAmount.checked_canonicalOrZero _ _ _ _ _ _ hmax ‹_›
    | exact STAmount.ofNumber_canonicalOrZero _ _ _ _ hmax ‹_›

/-- The amount a deposit rounds to is canonical-or-zero, in the vault's asset, and nonnegative. -/
lemma Vault.roundedDepositAmount_form (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hc : amountDeposit.Canonical) (hty : amountDeposit.mNumericType = v.numericType)
    (h : (v.roundedDepositAmount amountDeposit).run = .ok (.ok roundedAmount)) :
    roundedAmount.CanonicalOrZero ∧ roundedAmount.mNumericType = v.numericType ∧
      0 ≤ roundedAmount.toRat := by
  obtain ⟨assetsTotal, -, hcl, -⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount h
  obtain ⟨h1, h2, h3⟩ := clampToSumExponent_canonicalOrZero assetsTotal amountDeposit roundedAmount
    v.baseExponent (Or.inl hc) v.baseExponent_range.1 v.baseExponent_range.2 hcl
  exact ⟨h1, h2.trans hty, h3⟩

/-- The charge of a successful deposit computation is canonical-or-zero, in the vault's asset,
and nonnegative. -/
lemma computeDeposit_assets_form (v : Vault) (roundedAmount : STAmount) (isDonation : Bool)
    (amounts : VaultAmounts) (hra : roundedAmount.CanonicalOrZero)
    (hty : roundedAmount.mNumericType = v.numericType)
    (hmax : v.numericType.isIntegral = true → v.numericType.maxValue.toNat ≤ maxRep.toNat)
    (hok : (computeDeposit v roundedAmount isDonation).run = .ok (.ok amounts)) :
    amounts.assets.CanonicalOrZero ∧ amounts.assets.mNumericType = v.numericType ∧
      0 ≤ amounts.assets.toRat := by
  cases isDonation
  · obtain ⟨assets, assetsTotal, -, -, hsta, -, -, hcl, -⟩ :=
      computeDeposit_success_reduces v roundedAmount amounts hok
    obtain ⟨hf1, hf2⟩ := sharesToAssetsDeposit_form v amounts.shares assets hmax hsta
    obtain ⟨h1, h2, h3⟩ := clampToSumExponent_canonicalOrZero assetsTotal assets amounts.assets
      v.baseExponent hf1 v.baseExponent_range.1 v.baseExponent_range.2 hcl
    exact ⟨h1, h2.trans hf2, h3⟩
  · obtain ⟨assetsTotal, -, -, hcl, -⟩ := computeDeposit_donation_reduces v roundedAmount amounts hok
    obtain ⟨h1, h2, h3⟩ := clampToSumExponent_canonicalOrZero assetsTotal roundedAmount amounts.assets
      v.baseExponent hra v.baseExponent_range.1 v.baseExponent_range.2 hcl
    exact ⟨h1, h2.trans hty, h3⟩

/-- The inflow check returns `tesSUCCESS` or `tecLIMIT_EXCEEDED`. -/
lemma Vault.checkOpenLimit_codes (v : Vault) (amount : STAmount) (ter : TER)
    (h : v.checkOpenLimit amount = .ok ter) : ter = .tesSUCCESS ∨ ter = .tecLIMIT_EXCEEDED := by
  simp only [Vault.checkOpenLimit, bind, Except.bind, pure, Except.pure] at h
  walk_ok
  all_goals simp

/-- The cash update rejects with `tefBAD_LEDGER` or `tecLIMIT_EXCEEDED`. -/
lemma Vault.adjustAssetsAndShares_codes (v : Vault) (assets shares : STAmount) (ter : TER)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.error ter)) :
    ter = .tefBAD_LEDGER ∨ ter = .tecLIMIT_EXCEEDED :=
  Or.inl (Vault.adjustAssetsAndShares_rejected_bad_ledger v assets shares ter h)

/-- A successful cash update, step by step: it converts both amounts, adds the shares to the
share total, and stores the new cash rounded to the asset's precision. -/
lemma Vault.adjustAssetsAndShares_ok_reduces (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (h : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) :
    ∃ assetsNum sharesNum s aa' st' : Number, assets.toNumber .to_nearest = .ok assetsNum ∧
      shares.toNumber .to_nearest = .ok sharesNum ∧
      v.sharesTotal.operator_add sharesNum .to_nearest = .ok st' ∧
      v.assetsAvailable.operator_add assetsNum .to_nearest = .ok s ∧
      STAmount.roundToNumericType v.numericType s .to_nearest = .ok aa' ∧
      raw = { v.toRawVault with assetsAvailable := aa', sharesTotal := st' } := by
  simp only [Vault.adjustAssetsAndShares, Vault.adjustBalances] at h
  unfold_ter at h
  walk_ok
  simp only [Number.operator_add_zero_right, Except.ok.injEq] at *
  subst_vars
  exact ⟨_, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

/-- A lawful vault's share total fits the MPT maximum. -/
lemma Vault.sharesTotal_le_maxRep (v : Vault) : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
  have h := v.exact.sharesTotal_representable
  have h2 : (v.toExact.sharesTotal : ℚ) ≤ 9223372036854775807 := by
    exact_mod_cast (by omega : v.toExact.sharesTotal ≤ 9223372036854775807)
  rw [← hST]
  linarith

/-- Changing only the cash and the share total keeps a vault lawful when the new cash is nonnegative, stored and on
the grid, the new total is whole shares within the MPT maximum, and the empty-vault rule holds. -/
lemma Vault.cash_shares_update_lawful (v : Vault) (aa' st' : Number)
    (haa : aa'.isNormalized) (haa0 : 0 ≤ aa'.toRat)
    (haar : STAmount.isRounded v.numericType aa' = false)
    (haag : aa' = Number.zero ∨
      aa'.mantissa_.toNat % 10 ^ (v.numericType.baseExponent v.scale - aa'.exponent_).toNat = 0)
    (hst : st'.isNormalized) (hst0 : 0 ≤ st'.toRat) (hstd : st'.toRat.den = 1)
    (hstcap : st'.toRat ≤ 2 ^ 63 - 1)
    (hempty : st' = Number.zero → aa' = Number.zero ∧ v.assetsDeployed = Number.zero) :
    ({ v.toRawVault with assetsAvailable := aa', sharesTotal := st' } : RawVault).WF ∧
      ({ v.toRawVault with assetsAvailable := aa', sharesTotal := st' } : RawVault).Valid := by
  obtain ⟨_, hAD, hAR, hmax, _, hLU, hYU, _, _, hsi, hsl⟩ := v.wf
  obtain ⟨_, hADnn, hARnn, hLUnn, hYUnn, hmaxp, _, hLUle, hADr, hARle, _, hblk, hsched, hfee1, hfee2, -, -⟩ :=
    v.valid
  -- the share total is the whole number `k` of its numerator
  have hk : ((st'.toRat.num.toNat : ℕ) : ℚ) = st'.toRat := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hst0)]
    conv_rhs => rw [← Rat.num_div_den st'.toRat]
    rw [hstd]; simp
  have hkcap : st'.toRat.num.toNat ≤ 9223372036854775807 := by
    have : ((st'.toRat.num.toNat : ℕ) : ℚ) ≤ 9223372036854775807 := by rw [hk]; linarith
    exact_mod_cast this
  have hrep : STAmount.isRounded .int64 st' = false := by
    rw [STAmount.isRounded_eq_false_iff _ _ hst hst0]
    by_cases h0 : st'.toRat = 0
    · exact Or.inl h0
    · exact Or.inr ⟨by decide, st'.toRat.num.toNat, hkcap, by omega, hk.symm⟩
  refine ⟨⟨haa, hAD, hAR, hmax, hst, hLU, hYU, hst0, hstd, hsi, hsl⟩,
    ⟨?_, hADnn, hARnn, hLUnn, hYUnn, hmaxp, hempty, hLUle, hADr, hARle, hrep, hblk, hsched, hfee1, hfee2, haar,
      haag⟩⟩
  rw [operator_le_iff _ _ Number.zero_isNormalized haa, Number.toRat_zero]
  exact haa0

/-- The cash update adds a whole number of shares exactly while the new share total stays
within the `int64` range. -/
lemma Vault.adjustAssetsAndShares_sharesTotal (v : Vault) (assets shares : STAmount) (raw : RawVault)
    (hsc : shares.CanonicalOrZero) (hden : shares.toRat.den = 1)
    (hlo : -2 ^ 63 < v.sharesTotal.toRat + shares.toRat) (hhi : v.sharesTotal.toRat + shares.toRat < 2 ^ 63)
    (hadj : (v.adjustAssetsAndShares assets shares).run = .ok (.ok raw)) :
    raw.sharesTotal.toRat = v.sharesTotal.toRat + shares.toRat := by
  obtain ⟨assetsNum, sharesNum, s, aa', st', hnum, hsnum, hst, hs, haa, rfl⟩ :=
    Vault.adjustAssetsAndShares_ok_reduces v _ _ raw hadj
  obtain ⟨hsv, hsnorm⟩ := hsc.toNumber_exact sharesNum hsnum
  have hsden : sharesNum.toRat.den = 1 := by rw [hsv]; exact hden
  have hbound := Rat.num_natAbs_add_lt_of_den_one _ _ v.wf.sharesTotal_int hsden (by rw [hsv]; exact hlo)
    (by rw [hsv]; exact hhi)
  obtain ⟨hstv, -⟩ := operator_add_exact_int _ _ _ v.wf.sharesTotal_norm hsnorm v.wf.sharesTotal_int
    hsden hbound hst
  show st'.toRat = _
  rw [hstv, hsv]

end XRPL.Model.SingleAssetVault
