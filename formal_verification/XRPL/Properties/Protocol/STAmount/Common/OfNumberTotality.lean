import XRPL.Properties.Protocol.Number.Totality
import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Properties.Protocol.STAmount.Common.FracCanonZero

/-! # Forward totality of the integral `ofNumber` path

Integral `STAmount.ofNumber` sends a sign-cleared value through `Number.to_rep`
and repacks it with `STAmount.checked`. For a bounded value both steps succeed, and
a whole value within the numeric type's bound is stored exactly, so `isRounded`
is false on it. -/

namespace XRPL.Model.Protocol

/-- **A value within `2 ^ 63 - 1` has a nonpositive `Number.exponent`.** With a
mantissa above `maxRep` the accessor bumps the exponent by one, and a nonnegative
raw exponent would already push the value past `maxRep`. -/
lemma Number.exponent_le_zero_of_cap (n : Number) (hnorm : n.isNormalized)
    (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    n.exponent ≤ 0 := by
  have htoRat : n.toRat = (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
    Number.toRat_of_nonneg n hneg
  rcases hnorm with hz | ⟨hmlo, _hmhi, _, _hexp_lo, _hexp_hi⟩
  · rw [hz]; decide
  · unfold Number.exponent
    by_cases hgt : n.mantissa_ > maxRep
    · rw [if_pos hgt]
      by_contra hcon
      push Not at hcon
      have hexp_nn : (0 : ℤ) ≤ n.exponent_ := by omega
      have hpow_ge1 : (1 : ℚ) ≤ (10 : ℚ) ^ n.exponent_ := by
        rw [show n.exponent_ = ((n.exponent_.toNat : ℤ)) from by omega, zpow_natCast]
        exact one_le_pow₀ (by norm_num)
      have hm_ge : (9223372036854775808 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by
        have hlt := UInt64.lt_iff_toNat_lt.mp hgt
        rw [maxRep_val] at hlt
        have h2 : (9223372036854775808 : ℕ) ≤ n.mantissa_.toNat := by omega
        exact_mod_cast h2
      have hge : (9223372036854775808 : ℚ) ≤ n.toRat := by
        rw [htoRat]
        calc (9223372036854775808 : ℚ) = 9223372036854775808 * 1 := by ring
          _ ≤ (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_ :=
              mul_le_mul hm_ge hpow_ge1 (by norm_num) (by positivity)
      have : (9223372036854775808 : ℚ) ≤ 2 ^ 63 - 1 := le_trans hge hcap
      norm_num at this
    · rw [if_neg hgt]
      by_contra hcon
      push Not at hcon
      have hm_nat : (1000000000000000000 : ℕ) ≤ n.mantissa_.toNat := by
        have := UInt64.le_iff_toNat_le.mp hmlo; rwa [largeRange_min_val] at this
      have hm_q : (1000000000000000000 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hm_nat
      have hexp1 : 1 ≤ n.exponent_.toNat := by omega
      have hpow : (10 : ℚ) ≤ 10 ^ n.exponent_.toNat := by
        calc (10 : ℚ) = 10 ^ 1 := (pow_one 10).symm
          _ ≤ 10 ^ n.exponent_.toNat := pow_le_pow_right₀ (by norm_num) hexp1
      have hge : (10000000000000000000 : ℚ) ≤ n.toRat := by
        rw [htoRat, show n.exponent_ = (n.exponent_.toNat : ℤ) from by omega, zpow_natCast]
        calc (10000000000000000000 : ℚ) = 1000000000000000000 * 10 := by norm_num
          _ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_.toNat :=
              mul_le_mul hm_q hpow (by norm_num) (by positivity)
      have : (10000000000000000000 : ℚ) ≤ 2 ^ 63 - 1 := le_trans hge hcap
      norm_num at this


/-- The same bound on the raw `exponent_` field, for a nonnegative value. -/
lemma Number.exponent_raw_le_zero_of_cap (n : Number) (hnorm : n.isNormalized)
    (hnn : 0 ≤ n.toRat) (hcap : n.toRat ≤ 2 ^ 63 - 1) : n.exponent_ ≤ 0 := by
  have h := Number.exponent_le_zero_of_cap n hnorm (Number.negative_false_of_nonneg n hnorm hnn)
    hcap
  unfold Number.exponent at h
  split at h <;> omega

/-- `to_rep` of a sign-cleared `Number` at adjusted exponent `0` returns its
mantissa: nothing is shifted, grown or rounded. -/
lemma Number.to_rep_of_exponent_zero (n : Number) (mode : rounding_mode)
    (hneg : n.negative_ = false) (hexp : n.exponent = 0) :
    n.to_rep mode = .ok n.mantissa := by
  have hD0_range := Number.mantissa_range_of_nonneg n hneg
  unfold Number.to_rep
  simp only
  by_cases hz : (n.mantissa == 0) = true
  · rw [if_pos hz, beq_iff_eq.mp hz]
  · rw [if_neg hz, hneg]
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg (show ¬ n.exponent < 0 by omega), if_pos (show n.exponent ≥ 0 by omega)]
    have hgrow0 : Number.to_rep.grow n.mantissa n.exponent = .ok n.mantissa := by
      rw [Number.to_rep.grow, if_neg (show ¬ n.exponent > 0 from by omega)]
    rw [hgrow0]
    simp only
    have h_u64 : n.mantissa.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep n.mantissa hD0_range.1 hD0_range.2
    rw [pushOverflow_noop_of_le_maxRep_of_empty h_u64 Guard.new mode (by decide)]
    rw [show Guard.new.round mode = -2 from by
      have := start_guard_round mode false; simpa using this]
    rw [if_neg (show ¬ ((-2 : Int) == 1 || (-2 : Int) == 0 && n.mantissa % 2 == 1) = true
      from by simp)]
    rw [if_neg (show ¬ (maxRep.toInt64 < n.mantissa ∧ n.mantissa < maxRepUp.toInt64) from
      fun hc => by
        have := Int64.lt_iff_toInt_lt.mp hc.1
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
        omega)]

/-- **Forward totality of `Number.to_rep` on a nonnegative operand with nonpositive
`Number.exponent`.** `grow` is entered only at offset `0` and returns its input.
The floor-divide lands below `maxRep`, so the round-up bump never overflows. -/
lemma Number.to_rep_ok_of_nonneg_exp_nonpos (n : Number) (mode : rounding_mode)
    (hneg : n.negative_ = false) (hexp : n.exponent ≤ 0) :
    ∃ r : Int64, n.to_rep mode = .ok r := by
  by_cases hexp0 : n.exponent = 0
  · exact ⟨_, Number.to_rep_of_exponent_zero n mode hneg hexp0⟩
  have hexplt : n.exponent < 0 := by omega
  unfold Number.to_rep
  simp only
  by_cases hz : (n.mantissa == 0) = true
  · exact ⟨0, by rw [if_pos hz]⟩
  · rw [if_neg hz]
    have hD0_range := Number.mantissa_range_of_nonneg n hneg
    rw [hneg]
    simp only [Bool.false_eq_true, if_false]
    have hge : ¬ n.exponent ≥ 0 := by omega
    rw [if_pos hexplt, if_neg hge]
    simp only
    set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
    have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ (-n.exponent).toNat := by
      have := shift_fst_eq n.mantissa n.exponent Guard.new hD0_range.1
      rwa [← hspdef] at this
    have hsp_nn : 0 ≤ sp.1.toInt := by
      rw [hDf]; exact Int.ediv_nonneg hD0_range.1 (by positivity)
    have hsp_lt : sp.1.toInt < (maxRep.toNat : ℤ) := by
      have hk_ne : (10 : ℤ) ^ (-n.exponent).toNat ≠ 0 := by positivity
      have hmul : sp.1.toInt * 10 ^ (-n.exponent).toNat ≤ n.mantissa.toInt := by
        rw [hDf]; exact Int.ediv_mul_le _ hk_ne
      have h10le : (10 : ℤ) ≤ 10 ^ (-n.exponent).toNat := by
        calc (10 : ℤ) = 10 ^ 1 := by ring
          _ ≤ 10 ^ (-n.exponent).toNat := pow_le_pow_right₀ (by norm_num) (by omega)
      have hmul10 : sp.1.toInt * 10 ≤ n.mantissa.toInt :=
        le_trans (mul_le_mul_of_nonneg_left h10le hsp_nn) hmul
      have hle := hD0_range.2
      rw [maxRep_val] at hle ⊢
      omega
    have hsp_lt_u64 : sp.1.toUInt64.toNat < maxRep.toNat := by
      have hnat := toUInt64_toNat_of_nonneg sp.1 hsp_nn; omega
    rw [pushOverflow_noop_of_lt_maxRep hsp_lt_u64 sp.2 mode]
    by_cases hb : (sp.2.round mode == 1 || sp.2.round mode == 0 && sp.1 % 2 == 1) = true
    · rw [if_pos hb, if_neg (show ¬ sp.1 ≥ maxRep.toInt64 from fun hc => by
        have := Int64.le_iff_toInt_le.mp hc
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
        omega)]
      exact ⟨_, rfl⟩
    · rw [if_neg hb, if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from
        fun hc => by
          have := Int64.lt_iff_toInt_lt.mp hc.1
          rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
          omega)]
      exact ⟨_, rfl⟩

/-- **Forward totality of the integral `STAmount.canonicalize` against the type's
own bound.** An offset-`0`, sign-cleared integral record whose magnitude fits
`maxRep` and the type's `maxValue` canonicalizes without error. -/
lemma STAmount.canonicalize_integral_ok_of_le (s : STAmount) (mode : rounding_mode)
    (hint : s.integral = true) (hoff : s.mOffset = 0) (hsneg : s.mIsNegative = false)
    (hv : s.mValue.toNat ≤ maxRep.toNat)
    (hvmax : s.mValue.toNat ≤ s.mNumericType.maxValue.toNat)
    (hmaxoff : (0 : Int) ≤ s.mNumericType.maxOffset) :
    ∃ result, s.canonicalize mode = .ok result := by
  rw [STAmount.canonicalize, if_pos hint]
  by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
  · exact ⟨_, by rw [if_pos hz]⟩
  · rw [if_neg hz,
        if_neg (show ¬ s.mOffset > s.mNumericType.maxOffset from by rw [hoff]; omega)]
    simp only [IntAmount.ofNumber]
    set u := Number.unchecked s.mIsNegative s.mValue s.mOffset with hu
    have hun : u.negative_ = false := hsneg
    have hum : u.mantissa_ = s.mValue := rfl
    have hnotgt : ¬ u.mantissa_ > maxRep := by
      rw [hum, gt_iff_lt, UInt64.lt_iff_toNat_lt]
      omega
    have hexp : u.exponent = 0 := by
      unfold Number.exponent
      rw [if_neg hnotgt]
      exact hoff
    rw [Number.to_rep_of_exponent_zero u mode hun hexp]
    simp only []
    -- the stored magnitude is the record's own value
    have hm : u.mantissa.toInt = (s.mValue.toNat : ℤ) := by
      unfold Number.mantissa
      rw [if_neg hnotgt, if_neg (by rw [hun]; decide), hum]
      exact UInt64.toInt64_toInt_of_lt _ (by rw [maxRep_val] at hv; omega)
    rw [if_neg (show ¬ u.mantissa.toInt.natAbs.toUInt64 > s.mNumericType.maxValue from by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hm, Int.natAbs_natCast]
      have hlt64 : s.mValue.toNat < 2 ^ 64 := by
        have := UInt64.toNat_lt_size s.mValue
        rw [uint64_size_val] at this
        exact this
      rw [UInt64.toNat_ofNat_of_lt' (by rw [uint64_size_val]; exact hlt64)]
      omega)]
    exact ⟨_, rfl⟩

/-- On an integral type, a normalized nonnegative `Number` within `2 ^ 63 - 1`
converts by packing its `to_rep` integer, which lies in `[0, maxRep]`. -/
private lemma STAmount.ofNumber_integral_reduce (nt : NumericType) (n : Number)
    (mode : rounding_mode) (hnt : nt.isIntegral = true) (hnorm : n.isNormalized)
    (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    ∃ r : Int64, n.to_rep mode = .ok r ∧ 0 ≤ r.toInt ∧ r.toUInt64.toNat ≤ maxRep.toNat ∧
      STAmount.ofNumber nt n mode = STAmount.checked nt r.toUInt64 0 false mode := by
  have hexp0 : n.exponent ≤ 0 := Number.exponent_le_zero_of_cap n hnorm hneg hcap
  obtain ⟨r, hr⟩ := Number.to_rep_ok_of_nonneg_exp_nonpos n mode hneg hexp0
  have hrrng := Number.to_rep_nonneg_range n mode r hneg hr
  refine ⟨r, hr, hrrng.1, toUInt64_toNat_le_maxRep r hrrng.1 hrrng.2, ?_⟩
  unfold STAmount.ofNumber
  rw [if_pos hnt]
  set neg : Bool := decide (n.signum < 0) with hneg_def
  set working : Number := if neg then n.operator_neg else n with hw_def
  have hnegf : neg = false := by
    rw [hneg_def]
    apply decide_eq_false
    unfold Number.signum
    rw [hneg]; simp only [Bool.false_eq_true, if_false]
    split <;> norm_num
  have hwn : working = n := by rw [hw_def, hnegf]; simp only [Bool.false_eq_true, if_false]
  rw [hwn, hr]
  simp only []
  rw [hnegf]

/-- **Forward totality of the integral `STAmount.ofNumber`.** A normalized
nonnegative `Number` within `2 ^ 63 - 1` converts into any integral type whose
`maxValue` covers `maxRep` and whose `maxOffset` is nonnegative. -/
lemma STAmount.ofNumber_integral_ok_of_cap (nt : NumericType) (n : Number)
    (mode : rounding_mode) (hnt : nt.isIntegral = true)
    (hmaxval : maxRep.toNat ≤ nt.maxValue.toNat) (hmaxoff : (0 : Int) ≤ nt.maxOffset)
    (hnorm : n.isNormalized) (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, STAmount.ofNumber nt n mode = .ok result := by
  obtain ⟨r, hr, hr0, hru64, heq⟩ :=
    STAmount.ofNumber_integral_reduce nt n mode hnt hnorm hneg hcap
  rw [heq]
  obtain ⟨result, hres⟩ := STAmount.canonicalize_integral_ok_of_le
    (STAmount.unchecked nt r.toUInt64 0 false) mode hnt rfl rfl hru64 (le_trans hru64 hmaxval)
    hmaxoff
  exact ⟨result, by rw [STAmount.checked]; exact hres⟩

/-- An `int64` conversion of a normalized nonnegative `Number` bounded by
`2 ^ 63 - 1` succeeds in every mode. `NumericType.int64` carries
`maxValue = maxRep` and `maxOffset = 18`, so the general cap totality applies. -/
lemma STAmount.ofNumber_int64_ok (n : Number) (mode : rounding_mode)
    (hnorm : n.isNormalized) (hneg : n.negative_ = false) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, STAmount.ofNumber .int64 n mode = .ok result :=
  STAmount.ofNumber_integral_ok_of_cap .int64 n mode (by decide) (by decide) (by decide)
    hnorm hneg hcap

/-- **Forward totality of `operator_sub` for two normalized capped operands.**
Nonnegative normalized values at most `2 ^ 63 - 1` have a nonpositive exponent,
which gives `operator_sub_ok_of_exp` its headroom. -/
lemma Number.operator_sub_ok_of_normalized_cap (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxneg : x.negative_ = false) (hyneg : y.negative_ = false)
    (hxcap : x.toRat ≤ 2 ^ 63 - 1) (hycap : y.toRat ≤ 2 ^ 63 - 1) :
    ∃ result, x.operator_sub y mode = .ok result := by
  by_cases hy0 : y.mantissa_ = 0
  · exact ⟨x, Number.operator_sub_of_mantissa_zero x y mode hy0⟩
  · have hxe := Number.exponent_raw_le_zero_of_cap x hx
      (Number.toRat_nonneg_of_nonnegative x hxneg) hxcap
    have hye := Number.exponent_raw_le_zero_of_cap y hy
      (Number.toRat_nonneg_of_nonnegative y hyneg) hycap
    exact Number.operator_sub_ok_of_exp x y mode hx hy
      (by unfold maxExponent; omega) (by unfold maxExponent; omega)

/-- **Forward totality of the integral `STAmount.ofNumber` up to the type's own
bound.** A normalized, nonnegative whole `Number` within the type's `maxValue`
and `2 ^ 63 - 1` converts without error. -/
lemma STAmount.ofNumber_integral_ok_of_le (nt : NumericType) (n : Number)
    (mode : rounding_mode) (hnt : nt.isIntegral = true) (hmaxoff : (0 : Int) ≤ nt.maxOffset)
    (hnorm : n.isNormalized) (hneg : n.negative_ = false) (hden : n.toRat.den = 1)
    (hcap : n.toRat ≤ 2 ^ 63 - 1) (hmax : n.toRat ≤ nt.maxValue.toNat) :
    ∃ result, STAmount.ofNumber nt n mode = .ok result := by
  obtain ⟨r, hr, hr0, hru64, heq⟩ :=
    STAmount.ofNumber_integral_reduce nt n mode hnt hnorm hneg hcap
  rw [heq]
  -- `to_rep` returns the whole value itself, which fits the type's bound
  have hw := to_rep_within_one n mode r hnorm hr
  have hnum : (n.toRat.num : ℚ) = n.toRat := Rat.coe_int_num_of_den_eq_one hden
  have hreq : r.toInt = n.toRat.num := by
    have h1 : |((r.toInt - n.toRat.num : ℤ) : ℚ)| < 1 := by push_cast; rw [hnum]; exact hw
    have h2 : |r.toInt - n.toRat.num| < 1 := by exact_mod_cast h1
    have h3 := abs_lt.mp h2
    omega
  have hrmax : r.toUInt64.toNat ≤ nt.maxValue.toNat := by
    have hnat : (r.toUInt64.toNat : ℤ) = r.toInt := toUInt64_toNat_of_nonneg r hr0
    have h1 : (r.toInt : ℚ) ≤ nt.maxValue.toNat := by rw [hreq, hnum]; exact hmax
    have h2 : r.toInt ≤ nt.maxValue.toNat := by exact_mod_cast h1
    omega
  obtain ⟨result, hres⟩ := STAmount.canonicalize_integral_ok_of_le
    (STAmount.unchecked nt r.toUInt64 0 false) mode hnt rfl rfl hru64 hrmax hmaxoff
  exact ⟨result, by rw [STAmount.checked]; exact hres⟩

/-- **An integral type stores a bounded whole `Number` exactly.** A normalized,
nonnegative whole `Number` within the type's `maxValue` and `2 ^ 63 - 1` is not
rounded by the conversion to the asset. -/
lemma STAmount.isRounded_integral_eq_false (nt : NumericType) (n : Number)
    (hnt : nt.isIntegral = true) (hmaxoff : (0 : Int) ≤ nt.maxOffset)
    (hnorm : n.isNormalized) (h0 : 0 ≤ n.toRat) (hden : n.toRat.den = 1)
    (hcap : n.toRat ≤ 2 ^ 63 - 1) (hmax : n.toRat ≤ nt.maxValue.toNat) :
    STAmount.isRounded nt n = false := by
  have hneg := Number.negative_false_of_nonneg n hnorm h0
  obtain ⟨s, hs⟩ :=
    STAmount.ofNumber_integral_ok_of_le nt n .to_nearest hnt hmaxoff hnorm hneg hden hcap hmax
  have hval := STAmount.ofNumber_integral_exact nt n .to_nearest s hnt hnorm hden hs
  have hic := (STAmount.ofNumber_integral_canonical nt n .to_nearest s hnt hs).1
  have hsz : s.mValue.toNat ≤ 2 ^ 63 - 1 := by
    by_cases hs0 : s.mValue = 0
    · rw [hs0]
      decide
    · rcases STAmount.ofNumber_exactCanonical nt n .to_nearest s hnorm h0 hs hs0 with
        hiou | ⟨_, hsz⟩
      · have hf := hiou.is_fractional
        rw [STAmount.ofNumber_mNumericType _ _ _ _ hs] at hf
        rw [hf] at hnt
        exact absurd hnt (by decide)
      · exact hsz
  obtain ⟨sn, hsn, hsv, hsnn⟩ := STAmount.toNumber_integral_small_exact s .to_nearest hic hsz
  have heq : sn.operator_eq n = true :=
    (operator_eq_iff sn n hsnn hnorm).mpr (by rw [hsv, hval])
  unfold STAmount.isRounded STAmount.equalAfterNumberConvert
  simp [hs, hsn, heq, bind, Except.bind, pure, Except.pure]

end XRPL.Model.Protocol
