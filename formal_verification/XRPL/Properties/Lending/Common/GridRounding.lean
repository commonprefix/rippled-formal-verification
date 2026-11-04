import XRPL.Properties.Lending.Loan.Common.Grid
import XRPL.Properties.Lending.Common.SumRounding
import XRPL.Properties.Protocol.STAmount.Common.Representable

/-! # Roundings that stay on a grid

Rounding a whole number of `10^s` units, converting it to an `STAmount`, or flooring a sum onto a grid
at or above `s` never leaves the grid of `10^s`. Shared by the loan, ledger and loan-broker proofs. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault (Vault)

open private STAmount.ofNumber_integral_small from XRPL.Properties.Lending.Loan.Common.Grid

/-- A point of a grid is a point of every finer grid. -/
lemma Number.OnGrid.mono {s e : Int} {x : Number} (h : Number.OnGrid e x) (hse : s ≤ e) :
    Number.OnGrid s x := by
  obtain ⟨hx, k, hk⟩ := h
  refine ⟨hx, k * 10 ^ (e - s).toNat, ?_⟩
  rw [hk]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega),
    sub_add_cancel]

/-- A downward rounding of a whole number of units is on the grid: exact below `2^63` units, too large
otherwise. -/
lemma Number.OnGrid.of_lower {r : Number} {s : Int} {k : ℤ} (hr : r.isNormalized)
    (hR : r.RoundsToRepresentable ((k : ℚ) * 10 ^ s) .downward)
    (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1) : Number.OnGrid s r := by
  obtain ⟨n, hn, hrv⟩ := hR
  have hp : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
  have hle := Number.lower_le _ n hn
  by_cases hk : -2 ^ 63 < k ∧ k < 2 ^ 63
  · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow k s hk hs
    have hge := Number.lower_tight _ n hn w hw (le_of_eq hwv)
    rw [hwv] at hge
    exact ⟨hr, k, by rw [hrv]; linarith⟩
  · apply Number.OnGrid.of_large hr
    rw [hrv]
    have h18 : (10 : ℚ) ^ (18 : ℕ) ≤ 2 ^ 63 := by norm_num
    rcases not_and_or.mp hk with hk' | hk'
    · have hk2 : (k : ℚ) ≤ -2 ^ 63 := by exact_mod_cast (show k ≤ -2 ^ 63 by omega)
      have h1 : (k : ℚ) * 10 ^ s ≤ -((10 : ℚ) ^ (18 : ℕ) * 10 ^ s) := by
        rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (by linarith) hp.le
      have h2 : 0 < (10 : ℚ) ^ (18 : ℕ) * 10 ^ s := by positivity
      rw [abs_of_neg (by linarith)]
      linarith
    · obtain ⟨w, hw, hwv⟩ := Number.exists_normalized_int_mul_pow (10 ^ 18) s (by constructor <;> norm_num) hs
      push_cast at hwv
      have hk2 : (2 : ℚ) ^ 63 ≤ k := by exact_mod_cast (show 2 ^ 63 ≤ k by omega)
      have hwle : w.toRat ≤ (k : ℚ) * 10 ^ s := by
        rw [hwv]; exact mul_le_mul_of_nonneg_right (by linarith) hp.le
      have hge := Number.lower_tight _ n hn w hw hwle
      rw [hwv] at hge
      have h2 : 0 < (10 : ℚ) ^ 18 * 10 ^ s := by positivity
      rw [abs_of_nonneg (by linarith)]
      norm_num at hge ⊢
      linarith

/-- A downward difference of two grid points is on the grid. -/
lemma Number.OnGrid.sub_downward {s : Int} {x y d : Number} (hx : Number.OnGrid s x)
    (hy : Number.OnGrid s y) (hs : minExponent + 18 ≤ s ∧ s ≤ maxExponent - 1)
    (hok : x.operator_sub y .downward = .ok d) : Number.OnGrid s d := by
  obtain ⟨hxn, a, ha⟩ := hx
  obtain ⟨hyn, b, hb⟩ := hy
  have hdn := Number.operator_sub_isNormalized_any x y d .downward hxn hyn hok
  by_cases hd : d.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero d hdn hd]; exact Number.OnGrid.zero s
  · have hR := operator_sub_rounded_downward x y d hxn hyn hok hd
    rw [ha, hb, ← sub_mul, show (a : ℚ) - b = ((a - b : ℤ) : ℚ) by push_cast; ring] at hR
    exact Number.OnGrid.of_lower hdn hR hs

/-- A negative normalized `Number` whose mantissa ends in three zeros converts to `STAmount` exactly, in every
mode: the 16-digit amount drops those zeros and raises the exponent by `3`. -/
lemma STAmount.ofNumber_fractional_of_trailing_zeros_neg (n : Number) (mode : rounding_mode)
    (hn : n.isNormalized) (hm0 : n.mantissa_ ≠ 0) (hneg : n.negative_ = true)
    (hmod : n.mantissa_.toNat % 1000 = 0)
    (he_lo : (-96 : Int) ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 3 ≤ 80) :
    STAmount.ofNumber .fractional n mode =
      .ok ⟨.fractional, n.mantissa_ / 10 / 10 / 10, n.exponent_ + 3, true⟩ := by
  obtain ⟨hlo', hhi'⟩ := hn.mantissaBounds_nat hm0
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  -- the packing runs on the magnitude, which has the same mantissa and exponent
  have hwm : n.operator_neg.mantissa_ = n.mantissa_ := by unfold Number.operator_neg; simp [hm0]
  have hwe : n.operator_neg.exponent_ = n.exponent_ := by unfold Number.operator_neg; simp [hm0]
  have hwneg : n.operator_neg.negative_ = false := by unfold Number.operator_neg; simp [hm0, hneg]
  have hnorm := normalizeToRange_16_exact n.operator_neg mode (by rw [hwm]; exact hlo') (by rw [hwm]; exact hhi')
    (by rw [hwm]; exact hmod) (by rw [hwe]; unfold minExponent; omega) (by rw [hwe]; unfold maxExponent; omega)
  rw [hwneg, if_neg (by decide), hwm, hwe] at hnorm
  have hsig : decide (n.signum < 0) = true := by rw [Number.signum_neg_decide, hneg]
  unfold STAmount.ofNumber
  simp only [hsig, if_true]
  rw [if_neg (by decide)]
  rw [show n.operator_neg.normalizeToRange kMinValue kMaxValue mode =
    n.operator_neg.normalizeToRange cMinValue cMaxValue mode from rfl, hnorm]
  simp only
  rw [show (n.mantissa_ / 10 / 10 / 10).toInt64.toUInt64 = n.mantissa_ / 10 / 10 / 10 from
    UInt64.toUInt64_toInt64 _]
  -- the 16-digit record is already canonical, so `checked` keeps it
  exact STAmount.canonicalize_canonical_id _ mode
    ⟨rfl, by show 10 ^ 15 ≤ (n.mantissa_ / 10 / 10 / 10).toNat; omega,
      by show (n.mantissa_ / 10 / 10 / 10).toNat < 10 ^ 16; omega, he_lo, he_hi⟩

/-- A nonzero IOU `ofNumber` amount is canonical, at an exponent at least three above the source's. -/
lemma STAmount.ofNumber_frac_offset (r : Number) (mode : rounding_mode) (result : STAmount)
    (hr : r.isNormalized) (hok : STAmount.ofNumber .fractional r mode = .ok result) (hresult : result.mValue ≠ 0) :
    result.IOUCanonical ∧ r.exponent_ + 3 ≤ result.mOffset := by
  have hr_ne := STAmount.ofNumber_source_ne_zero .fractional r mode result hok hresult
  obtain ⟨hr_lo, hr_hi⟩ := hr.mantissaBounds_nat hr_ne
  have hre_lo : minExponent ≤ r.exponent_ := by
    rcases hr with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show r.mantissa_ = 0 by rw [h0]; rfl) hr_ne
    · exact hlo
  set neg : Bool := decide (r.signum < 0) with hneg_def
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_mant : working.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : working.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp only [if_true]; unfold Number.operator_neg; rw [if_neg (by simpa using hr_ne)]
  have hw_neg : working.negative_ = false := by
    rw [hw_def, hneg_def, Number.signum_neg_decide]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hexp_hi3 : working.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi working mode mant exp hw_lo hw_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts working mode mant exp hw_lo hw_hi (by rw [hw_exp]; omega) hexp_hi3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn.1 hw_neg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    obtain ⟨hexp_lo80, hexp_hi80, hres_eq⟩ :=
      STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg mode rfl
        hmtu_lo hmtu_hi (by omega) hexp_le result hok hresult
    rw [hres_eq]
    exact ⟨⟨rfl, hmtu_lo, hmtu_hi, hexp_lo80, hexp_hi80⟩, by rw [hw_exp] at hexp_lo3; exact hexp_lo3⟩

/-- An IOU amount of a grid point is a grid point, in either sign: a coarse amount sits on a coarser grid,
and a fine one is the source itself. -/
lemma STAmount.ofNumber_frac_grid (x : Number) (s : Int) (mode : rounding_mode) (st : STAmount)
    (hx : Number.OnGrid s x) (hs : -80 ≤ s) (hof : STAmount.ofNumber .fractional x mode = .ok st) :
    ∃ k : ℤ, st.toRat = (k : ℚ) * 10 ^ s := by
  by_cases hz : st.mValue = 0
  · exact ⟨0, by rw [(STAmount.toRat_eq_zero_iff st).mpr hz]; simp⟩
  obtain ⟨hc, hoff⟩ := STAmount.ofNumber_frac_offset x mode st hx.1 hof hz
  by_cases hse : s ≤ st.mOffset
  · -- a coarse amount: its digits sit at or above the grid
    have hsplit : (10 : ℚ) ^ st.mOffset = (10 : ℚ) ^ (st.mOffset - s).toNat * 10 ^ s := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega),
        sub_add_cancel]
    cases hneg : st.mIsNegative
    · refine ⟨(st.mValue.toNat : ℤ) * 10 ^ (st.mOffset - s).toNat, ?_⟩
      rw [STAmount.toRat_of_nonneg st hneg, hsplit]; push_cast; ring
    · refine ⟨-((st.mValue.toNat : ℤ) * 10 ^ (st.mOffset - s).toNat), ?_⟩
      rw [STAmount.toRat_of_neg st hneg, hsplit]; push_cast; ring
  -- a fine amount: the source's mantissa ends in zeros, so the amount is the source
  push Not at hse
  have hxm : x.mantissa_ ≠ 0 := STAmount.ofNumber_source_ne_zero .fractional x mode st hof hz
  obtain ⟨hxn, k, hk⟩ := hx
  have habs := abs_toRat_eq x
  obtain ⟨-, hm19⟩ := hxn.mantissaBounds_nat hxm
  have hp : (0 : ℚ) < 10 ^ s := zpow_pos (by norm_num) _
  have hpx : (0 : ℚ) < 10 ^ x.exponent_ := zpow_pos (by norm_num) _
  have hsplit : (10 : ℚ) ^ s = (10 : ℚ) ^ (s - x.exponent_).toNat * 10 ^ x.exponent_ := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega),
      sub_add_cancel]
  have hmant : x.mantissa_.toNat = k.natAbs * 10 ^ (s - x.exponent_).toNat := by
    have h1 : (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ = ((k.natAbs * 10 ^ (s - x.exponent_).toNat : ℕ) : ℚ) *
        10 ^ x.exponent_ := by
      rw [← habs, hk, abs_mul, abs_of_pos hp, hsplit]
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs]
      ring
    exact_mod_cast mul_right_cancel₀ hpx.ne' h1
  have hmod : x.mantissa_.toNat % 1000 = 0 := by
    rw [hmant]
    have : 10 ^ (s - x.exponent_).toNat = 10 ^ 3 * 10 ^ ((s - x.exponent_).toNat - 3) := by
      rw [← pow_add]; congr 1; omega
    rw [this, Nat.mul_mod, Nat.mul_mod (10 ^ 3)]
    simp
  -- the source is at least one grid unit, so its exponent is in range
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ = 0 := by rw [← habs, hk]; simp
    rcases mul_eq_zero.mp this with h | h
    · exact hxm (by exact_mod_cast UInt64.toNat_inj.mp (by exact_mod_cast h))
    · exact absurd h hpx.ne'
  have hxe : s < x.exponent_ + 19 := by
    by_contra hc
    push Not at hc
    have h1 : (x.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hm19
    have h2 : (10 : ℚ) ^ (19 : ℕ) * 10 ^ x.exponent_ ≤ 10 ^ s := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      exact zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
    have h3 : (10 : ℚ) ^ s ≤ |x.toRat| := by
      rw [hk, abs_mul, abs_of_pos hp]
      have : (1 : ℚ) ≤ |(k : ℚ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
      nlinarith
    rw [habs] at h3
    nlinarith
  have hfine : STAmount.ofNumber .fractional x mode =
      .ok ⟨.fractional, x.mantissa_ / 10 / 10 / 10, x.exponent_ + 3, x.negative_⟩ := by
    cases hneg : x.negative_
    · exact STAmount.ofNumber_fractional_of_trailing_zeros x mode hxn hxm hneg hmod (by omega)
        (by have := hc.exp_hi; omega)
    · exact STAmount.ofNumber_fractional_of_trailing_zeros_neg x mode hxn hxm hneg hmod (by omega)
        (by have := hc.exp_hi; omega)
  rw [hfine, Except.ok.injEq] at hof
  subst hof
  have hm3 : (x.mantissa_ / 10 / 10 / 10).toNat = x.mantissa_.toNat / 1000 := m_div_thousand_toNat x.mantissa_
  have hval : ((x.mantissa_ / 10 / 10 / 10).toNat : ℚ) * 10 ^ (x.exponent_ + 3) =
      (x.mantissa_.toNat : ℚ) * 10 ^ x.exponent_ := by
    rw [hm3, zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    have : ((x.mantissa_.toNat / 1000 : ℕ) : ℚ) = (x.mantissa_.toNat : ℚ) / 1000 := by
      rw [Nat.cast_div (Nat.dvd_of_mod_eq_zero hmod) (by norm_num)]; norm_num
    rw [this]; norm_num; ring
  refine ⟨k, ?_⟩
  rw [← hk]
  cases hneg : x.negative_
  · rw [STAmount.toRat_of_nonneg _ rfl, Number.toRat_of_nonneg x hneg]; exact hval
  · rw [STAmount.toRat_of_neg _ rfl, Number.toRat_of_neg x hneg]; simp only at hval ⊢; rw [hval]

/-- An IOU amount of a grid point converts back to a grid point. -/
lemma STAmount.ofNumber_frac_onGrid (x : Number) (s : Int) (mode mode' : rounding_mode) (st : STAmount)
    (m : Number) (hx : Number.OnGrid s x) (hs : -80 ≤ s) (hof : STAmount.ofNumber .fractional x mode = .ok st)
    (hm : st.toNumber mode' = .ok m) : Number.OnGrid s m := by
  have hmn := STAmount.toNumber_isNormalized st mode' m hm
  have hfc := STAmount.ofNumber_fractional_fczr x mode st hof
  obtain ⟨k, hk⟩ := STAmount.ofNumber_frac_grid x s mode st hx hs hof
  by_cases hz : st.mValue = 0
  · have hint : st.integral = false := by unfold STAmount.integral; rw [hfc.1]; rfl
    rw [STAmount.toNumber_zero_fractional st mode' hint hz, Except.ok.injEq] at hm
    subst hm
    exact Number.OnGrid.zero s
  obtain ⟨hc, -⟩ := STAmount.ofNumber_frac_offset x mode st hx.1 hof hz
  obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact st mode' hc
  rw [hsn, Except.ok.injEq] at hm
  subst hm
  exact ⟨hmn, k, by rw [hv, hk]⟩

/-- An integral amount converts back to a whole number. -/
lemma STAmount.ofNumber_integral_onGrid (nt : NumericType) (x : Number) (mode mode' : rounding_mode)
    (st : STAmount) (m : Number) (hi : nt.isIntegral = true) (hof : STAmount.ofNumber nt x mode = .ok st)
    (hm : st.toNumber mode' = .ok m) : Number.OnGrid 0 m := by
  obtain ⟨hc, -⟩ := STAmount.ofNumber_integral_canonical nt x mode st hi hof
  obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact st mode' hc
    (STAmount.ofNumber_integral_small nt x mode st hi hof)
  rw [hsn, Except.ok.injEq] at hm
  subst hm
  refine ⟨STAmount.toNumber_isNormalized st mode' sn hsn, st.signedDrops, ?_⟩
  rw [hv, STAmount.IntegralCanonical.toRat_eq_signedDrops st hc, zpow_zero, mul_one]

/-- An amount of a grid point converts back to a grid point, at the unit grid for an integral asset. -/
lemma STAmount.ofNumber_onGrid (nt : NumericType) (x : Number) (s : Int) (mode mode' : rounding_mode)
    (st : STAmount) (m : Number) (hx : Number.OnGrid s x) (hs : -80 ≤ s) (hint : nt.isIntegral = true → s = 0)
    (hof : STAmount.ofNumber nt x mode = .ok st) (hm : st.toNumber mode' = .ok m) : Number.OnGrid s m := by
  by_cases hi : nt.isIntegral = true
  · rw [hint hi]; exact STAmount.ofNumber_integral_onGrid nt x mode mode' st m hi hof hm
  · have hfr : nt = .fractional := NumericType.eq_fractional_of_not_integral (by simpa using hi)
    subst hfr
    exact STAmount.ofNumber_frac_onGrid x s mode mode' st m hx hs hof hm

/-- Rounding a grid point to the asset gives a grid point. -/
lemma STAmount.roundToNumericType_onGrid_none (nt : NumericType) (x r : Number) (s : Int)
    (mode : rounding_mode) (hx : Number.OnGrid s x) (hs : -80 ≤ s) (hint : nt.isIntegral = true → s = 0)
    (h : STAmount.roundToNumericType nt x mode = .ok r) : Number.OnGrid s r := by
  unfold STAmount.roundToNumericType at h
  cases hof : STAmount.ofNumber nt x mode with
  | error e => rw [hof] at h; cases h
  | ok st =>
    rw [hof] at h
    exact STAmount.ofNumber_onGrid nt x s mode mode st r hx hs hint hof h

/-- A credit floored onto the posterior grid is on the base grid when the balance it lands on is: the
floored sum is on a grid at or above the base, and the credit is that sum less the balance. -/
lemma sumRoundAndSubtract_onGrid (A c : Number) (b : Int) (nt : NumericType) (mode' : rounding_mode)
    (st : STAmount) (m : Number) (hA : Number.OnGrid b A) (hb : -10 ≤ b ∧ b ≤ 0)
    (hint : nt.isIntegral = true → b = 0) (h : sumRoundAndSubtract A c b nt .downward = .ok st)
    (hm : st.toNumber mode' = .ok m) : Number.OnGrid b m := by
  unfold sumRoundAndSubtract at h
  by_cases hi : nt.isIntegral = true
  · rw [if_pos hi] at h
    obtain ⟨x, hx, h⟩ := bind_ok_peel _ _ _ h
    obtain rfl : x = st := Except.ok.inj h
    rw [hint hi]
    exact STAmount.ofNumber_integral_onGrid nt c _ mode' x m hi hx hm
  · rw [if_neg hi] at h
    obtain ⟨_, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨E, hE, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨sum, -, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨sum', hsum', h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨d, hd, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨_, -, hn⟩ := postSumExponent_reduces _ _ _ _ _ hE
    have hbE := numberExponent_ge _ _ _ _ hn
    have hErange := (postSumExponent_range _ _ _ _ _ (by omega) (by omega) hE).2
    have h1 := STAmount.roundToNumericType_onGrid nt sum sum' .downward E ⟨by omega, hErange.2⟩
      (fun h' => absurd h' hi) hsum'
    have h2 := Number.OnGrid.sub_downward (h1.mono hbE) hA
      ⟨by unfold minExponent; omega, by unfold maxExponent; omega⟩ hd
    exact STAmount.ofNumber_onGrid nt d b .downward mode' st m h2 (by omega) (fun h' => absurd h' hi) h hm

/-- The base exponent of an IOU vault is in the range of the grid lemmas. -/
lemma Vault.baseExponent_grid (v : Vault) :
    -10 ≤ v.baseExponent ∧ minExponent + 18 ≤ v.baseExponent ∧ v.baseExponent ≤ maxExponent - 1 := by
  obtain ⟨hblo, hbhi, -⟩ := v.baseExponent_bounds
  exact ⟨hblo, by unfold minExponent; omega, by unfold maxExponent; omega⟩

/-- A grid point of `10^b` between zero and `9 * 10^15` units is a whole number of units within `9 * 10^15`. -/
lemma Number.OnGrid.units_le (c : Number) (b : Int) (hg : Number.OnGrid b c) (h0 : 0 ≤ c.toRat)
    (hle : c.toRat ≤ 9 * 10 ^ 15 * (10 : ℚ) ^ b) :
    ∃ k : ℕ, k ≤ 9 * 10 ^ 15 ∧ c.toRat = (k : ℚ) * (10 : ℚ) ^ b := by
  obtain ⟨-, j, hj⟩ := hg
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hj0 : 0 ≤ j := by
    have : (0 : ℚ) ≤ (j : ℚ) * 10 ^ b := hj ▸ h0
    exact_mod_cast nonneg_of_mul_nonneg_left this hp
  have hjle : j ≤ 9 * 10 ^ 15 := by
    have : (j : ℚ) * 10 ^ b ≤ 9 * 10 ^ 15 * 10 ^ b := hj ▸ hle
    exact_mod_cast le_of_mul_le_mul_right this hp
  refine ⟨j.toNat, by omega, ?_⟩
  rw [hj]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hj0).symm

/-- Up to `9 * 10^15` whole units of `10^b` are stored exactly, when an XRP or MPT asset admits offset `0`
and the amount is within its maximum. -/
lemma STAmount.isRounded_false_of_units (nt : NumericType) (c : Number) (b : Int) (k : ℕ)
    (hn : c.isNormalized) (hv : c.toRat = (k : ℚ) * (10 : ℚ) ^ b) (hk : k ≤ 9 * 10 ^ 15)
    (hb : (-10 : ℤ) ≤ b ∧ b ≤ 0) (hint : nt.isIntegral = true → b = 0)
    (hmax : nt.isIntegral = true → k ≠ 0 → 0 ≤ nt.maxOffset ∧ k ≤ nt.maxValue.toNat) :
    STAmount.isRounded nt c = false := by
  have h0 : 0 ≤ c.toRat := by rw [hv]; positivity
  rw [STAmount.isRounded_eq_false_iff nt c hn h0, hv]
  cases hnt : nt with
  | fractional =>
    exact STAmount.representable_fractional_of_units k b (by omega) (by omega) (by omega)
  | integral maxValue maxOffset mulSqrt mulShift =>
    rw [hnt] at hint hmax
    have hb0 : b = 0 := hint rfl
    subst hb0
    by_cases hk0 : k = 0
    · exact Or.inl (by rw [hk0]; simp)
    · obtain ⟨hoff, hkm⟩ := hmax rfl hk0
      exact Or.inr ⟨hoff, k, hkm, by omega, by simp⟩

/-- Converting a value the asset stores exactly to an amount keeps the value. -/
lemma STAmount.ofNumber_eq_of_isRounded_false (nt : NumericType) (x : Number) (st : STAmount)
    (hn : x.isNormalized) (h0 : 0 ≤ x.toRat) (h : STAmount.isRounded nt x = false)
    (hok : STAmount.ofNumber nt x .to_nearest = .ok st) : st.toRat = x.toRat := by
  unfold STAmount.isRounded STAmount.equalAfterNumberConvert at h
  rw [hok] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hsn : st.toNumber .to_nearest with
  | error e => rw [hsn] at h; exact absurd h (by simp)
  | ok n =>
    rw [hsn] at h
    have heq : n.operator_eq x = true := by simpa using h
    have hnv : n.toRat = st.toRat := by
      by_cases hz : st.mValue = 0
      · exact (STAmount.toNumber_zero_facts st _ n hz hsn).1
      · exact (STAmount.toNumber_exact_of st n (STAmount.ofNumber_exactCanonical nt x _ st hn h0 hok hz) hsn).1
    rw [← hnv]
    exact (operator_eq_iff n x (STAmount.toNumber_isNormalized st _ n hsn) hn).mp heq

/-- A whole number of grid units floors to itself. -/
lemma floor_units_self (x : ℚ) (b : Int) (k : ℤ) (hx : x = (k : ℚ) * 10 ^ b) :
    (⌊x / 10 ^ b⌋ : ℚ) * 10 ^ b = x := by
  have hp : (10 : ℚ) ^ b ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [hx, mul_div_assoc, div_self hp, mul_one, Int.floor_intCast]

/-- A value floored onto a grid is at most the value and above it by less than one unit. -/
lemma floor_units_bounds (x : ℚ) (b : Int) :
    (⌊x / 10 ^ b⌋ : ℚ) * 10 ^ b ≤ x ∧ x - (⌊x / 10 ^ b⌋ : ℚ) * 10 ^ b < 10 ^ b := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have h1 := Int.floor_le (x / 10 ^ b)
  have h2 := Int.lt_floor_add_one (x / 10 ^ b)
  rw [le_div_iff₀ hp] at h1
  rw [div_lt_iff₀ hp] at h2
  constructor <;> nlinarith

/-- A whole number of `10^(b - 15)` floors onto the grid of `10^b` losing at most `1 - 10^-15` units. -/
private lemma floor_units_error_le (x : ℚ) (b : Int) (n : ℤ) (hx : x = (n : ℚ) * 10 ^ (b - 15)) :
    x - (⌊x / 10 ^ b⌋ : ℚ) * 10 ^ b ≤ (1 - 1 / 10 ^ 15) * 10 ^ b := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hx' : x = (n : ℚ) / 10 ^ 15 * 10 ^ b := by
    rw [hx, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), show (10 : ℚ) ^ (15 : ℤ) = 10 ^ (15 : ℕ) from by norm_num]
    ring
  have hdiv : x / 10 ^ b = (n : ℚ) / 10 ^ 15 := by
    rw [hx', mul_div_assoc, div_self hp.ne', mul_one]
  obtain ⟨f, hf⟩ : ∃ f, ⌊x / 10 ^ b⌋ = f := ⟨_, rfl⟩
  have h2 := Int.lt_floor_add_one (x / 10 ^ b)
  rw [hf, hdiv, div_lt_iff₀ (by norm_num : (0 : ℚ) < 10 ^ 15)] at h2
  have h3 : n < (f + 1) * 10 ^ 15 := by exact_mod_cast h2
  have h4 : n ≤ f * 10 ^ 15 + (10 ^ 15 - 1) := by linarith
  have h5 : (n : ℚ) ≤ (f : ℚ) * 10 ^ 15 + (10 ^ 15 - 1) := by exact_mod_cast h4
  rw [hf, hx']
  have h6 : (n : ℚ) / 10 ^ 15 - f ≤ 1 - 1 / 10 ^ 15 := by
    rw [div_sub' (by norm_num), div_le_iff₀ (by norm_num)]
    linarith
  nlinarith

/-- A canonical amount of at least `10^b` is a whole number of `10^(b - 15)`: its 16 digits reach at most
15 places below `10^b`. -/
private lemma canonical_toRat_fine_units (a : STAmount) (hc : a.Canonical) (b : Int) (hb : b ≤ 0)
    (hge : (10 : ℚ) ^ b ≤ a.toRat) : ∃ n : ℤ, a.toRat = (n : ℚ) * 10 ^ (b - 15) := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hpos : 0 < a.toRat := lt_of_lt_of_le hp hge
  have habs := STAmount.abs_toRat a
  rw [abs_of_pos hpos] at habs
  cases hi : a.integral with
  | true =>
    have hoff := (hc.1 hi).1.offset_zero
    rw [hoff, zpow_zero, mul_one] at habs
    refine ⟨(a.mValue.toNat : ℤ) * 10 ^ (15 - b).toNat, ?_⟩
    rw [habs]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega)]
    simp
  | false =>
    have hiou := hc.2 hi
    have hq : b - 15 ≤ a.mOffset := by
      have hlt : (10 : ℚ) ^ b < 10 ^ (16 + a.mOffset) := by
        calc (10 : ℚ) ^ b ≤ a.toRat := hge
          _ = (a.mValue.toNat : ℚ) * 10 ^ a.mOffset := habs
          _ < (10 : ℚ) ^ 16 * 10 ^ a.mOffset := by
            apply mul_lt_mul_of_pos_right _ (zpow_pos (by norm_num) _)
            exact_mod_cast hiou.mant_hi
          _ = 10 ^ (16 + a.mOffset) := by
            rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
            norm_cast
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).mp hlt
      omega
    refine ⟨(a.mValue.toNat : ℤ) * 10 ^ (a.mOffset - (b - 15)).toNat, ?_⟩
    rw [habs]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), Int.toNat_of_nonneg (by omega)]
    congr 2
    ring

/-- Flooring a canonical amount onto the grid of `10^b` loses at most `1 - 10^-15` units when the result is
positive: the amount is then at least `10^b`, so its 16 digits reach at most 15 places below `10^b`. -/
lemma floor_units_error_le_of_canonical (a : STAmount) (hc : a.Canonical) (b : Int) (hb : b ≤ 0)
    (hpos : 0 < (⌊a.toRat / 10 ^ b⌋ : ℚ) * 10 ^ b) :
    a.toRat - (⌊a.toRat / 10 ^ b⌋ : ℚ) * 10 ^ b ≤ (1 - 1 / 10 ^ 15) * 10 ^ b := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  have hf : (0 : ℚ) < ⌊a.toRat / 10 ^ b⌋ := (mul_pos_iff_of_pos_right hp).mp hpos
  have hf1 : (1 : ℚ) ≤ ⌊a.toRat / 10 ^ b⌋ := by
    have : 0 < ⌊a.toRat / 10 ^ b⌋ := by exact_mod_cast hf
    exact_mod_cast this
  have hle := Int.floor_le (a.toRat / 10 ^ b)
  have hge : (10 : ℚ) ^ b ≤ a.toRat := by
    rw [le_div_iff₀ hp] at hle
    nlinarith
  obtain ⟨n, hn⟩ := canonical_toRat_fine_units a hc b hb hge
  exact floor_units_error_le a.toRat b n hn

/-- A value floored onto the grid is not negative when the value is not. -/
lemma floor_units_nonneg (x : ℚ) (b : Int) (hx : 0 ≤ x) : 0 ≤ (⌊x / 10 ^ b⌋ : ℚ) * 10 ^ b := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  exact mul_nonneg (by exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hx hp.le)) hp.le

/-- Flooring the smaller of a value and a grid point gives the smaller of the floored value and the
point. -/
lemma floor_min_grid (x C : ℚ) (b : Int) (k : ℤ) (hC : C = (k : ℚ) * 10 ^ b) :
    (⌊min x C / 10 ^ b⌋ : ℚ) * 10 ^ b = min ((⌊x / 10 ^ b⌋ : ℚ) * 10 ^ b) C := by
  have hp : (0 : ℚ) < 10 ^ b := zpow_pos (by norm_num) _
  rcases le_total x C with h | h
  · rw [min_eq_left h, min_eq_left (le_trans (floor_units_bounds x b).1 h)]
  · rw [min_eq_right h, floor_units_self C b k hC, min_eq_right]
    calc C = (⌊C / 10 ^ b⌋ : ℚ) * 10 ^ b := (floor_units_self C b k hC).symm
      _ ≤ (⌊x / 10 ^ b⌋ : ℚ) * 10 ^ b := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact_mod_cast Int.floor_le_floor (div_le_div_of_nonneg_right h hp.le)

/-- A positive whole number of units counts at least one unit. -/
lemma units_pos {x : ℚ} {j : ℕ} {b : Int} (hj : x = (j : ℚ) * 10 ^ b) (hx : 0 < x) : 0 < j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    simp at hj
    linarith
  · exact h

/-- Taking `p` and then `q` out of `C`, each capped at what is left, takes `min (p + q) C`. -/
lemma min_add_min_sub (p q C : ℚ) (hq : 0 ≤ q) :
    min p C + min q (C - min p C) = min (p + q) C := by
  simp only [min_def]
  split_ifs <;> linarith

end XRPL.Model.Lending
