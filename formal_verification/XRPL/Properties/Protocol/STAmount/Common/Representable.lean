import XRPL.Properties.Protocol.STAmount.Common.OfNumberTotality
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Protocol.Common.Reduction

/-! # Amounts an asset stores exactly

`STAmount.isRounded nt value = false` says converting `value` to an amount of type `nt` keeps it.
`STAmount.Representable` is the same condition on the exact value. -/

namespace XRPL.Model.Protocol

/-- The exact reading of `STAmount.isRounded nt value = false` for a nonnegative value: zero, a
whole number within the integral type's bounds, or a 16-digit IOU mantissa in the IOU offset range. -/
def STAmount.Representable (nt : NumericType) (value : ℚ) : Prop :=
  value = 0 ∨
    match nt with
    | .integral maxValue maxOffset _ _ =>
      0 ≤ maxOffset ∧ ∃ k : ℕ, k ≤ maxValue.toNat ∧ k ≤ 2 ^ 63 - 1 ∧ value = k
    | .fractional =>
      ∃ (m : ℕ) (e : ℤ), 10 ^ 15 ≤ m ∧ m < 10 ^ 16 ∧ -96 ≤ e ∧ e ≤ 80 ∧
        value = (m : ℚ) * (10 : ℚ) ^ e

/-- `Number.zero` is exact for any asset. -/
lemma STAmount.isRounded_zero (nt : NumericType) : STAmount.isRounded nt Number.zero = false := by
  cases nt <;> rfl

/-- A nonzero integral amount passes the offset check, so the type allows offset `0`. -/
lemma STAmount.ofNumber_integral_maxOffset_nonneg (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount) (hnt : nt.isIntegral = true)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hres : result.mValue ≠ 0) :
    0 ≤ nt.maxOffset := by
  unfold STAmount.ofNumber at hok
  rw [if_pos hnt] at hok
  cases hrep : (if decide (n.signum < 0) = true then n.operator_neg else n).to_rep mode with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    obtain ⟨v, -, hok⟩ := bind_ok_peel _ _ _ hok
    rw [STAmount.checked, STAmount.canonicalize,
      if_pos (show (STAmount.unchecked nt v 0 (decide (n.signum < 0))).integral = true
        from hnt)] at hok
    simp only [STAmount.unchecked] at hok
    split at hok
    · exact absurd (by rw [← Except.ok.inj hok]) hres
    · split at hok
      · exact absurd hok (by simp)
      · omega

/-- A value `isRounded` keeps comes back from its amount with the same exact value. -/
private lemma STAmount.roundtrip_of_isRounded_false (nt : NumericType) (value : Number)
    (hn : value.isNormalized) (h : STAmount.isRounded nt value = false) :
    ∃ st n, STAmount.ofNumber nt value .to_nearest = .ok st ∧ st.toNumber .to_nearest = .ok n ∧
      n.toRat = value.toRat := by
  unfold STAmount.isRounded at h
  cases hconv : STAmount.equalAfterNumberConvert nt value with
  | error e => rw [hconv] at h; exact absurd h (by simp)
  | ok b =>
    rw [hconv] at h
    have hb : b = true := by cases b <;> simp at h ⊢
    subst hb
    unfold STAmount.equalAfterNumberConvert at hconv
    obtain ⟨st, hst, hconv⟩ := bind_ok_peel _ _ _ hconv
    obtain ⟨n, hnum, hconv⟩ := bind_ok_peel _ _ _ hconv
    have heq : n.operator_eq value = true :=
      Except.ok.inj (show (Except.ok (n.operator_eq value) : Except Error Bool) = .ok true from hconv)
    exact ⟨st, n, hst, hnum,
      (operator_eq_iff n value (STAmount.toNumber_isNormalized st _ n hnum) hn).mp heq⟩

/-- An amount the asset stores exactly converts to it without throwing. -/
lemma STAmount.ofNumber_ok_of_isRounded_false (nt : NumericType) (x : Number)
    (h : STAmount.isRounded nt x = false) : ∃ s, STAmount.ofNumber nt x .to_nearest = .ok s := by
  unfold STAmount.isRounded STAmount.equalAfterNumberConvert at h
  cases hc : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hc] at h; simp [bind, Except.bind] at h
  | ok s => exact ⟨s, rfl⟩

/-- An amount that holds the value exactly converts back to it, so `isRounded` is false. -/
private lemma STAmount.isRounded_false_of_exact (nt : NumericType) (value : Number) (st : STAmount)
    (hn : value.isNormalized) (hok : STAmount.ofNumber nt value .to_nearest = .ok st)
    (hc : st.ExactCanonical) (hval : st.toRat = value.toRat) :
    STAmount.isRounded nt value = false := by
  obtain ⟨sn, hsn, hv, hsnorm⟩ := STAmount.toNumber_exact_canonical st .to_nearest hc
  have heq : sn.operator_eq value = true := (operator_eq_iff sn value hsnorm hn).mpr (hv.trans hval)
  have hconv : STAmount.equalAfterNumberConvert nt value = .ok true := by
    unfold STAmount.equalAfterNumberConvert
    rw [hok]
    show (do let numValue ← st.toNumber .to_nearest
             pure (numValue.operator_eq value)) = .ok true
    rw [hsn]
    show Except.ok (sn.operator_eq value) = _
    rw [heq]
  unfold STAmount.isRounded
  rw [hconv]
  rfl

/-- `STAmount.isRounded` read exactly, for a normalized nonnegative amount. -/
theorem STAmount.isRounded_eq_false_iff (nt : NumericType) (value : Number) (hn : value.isNormalized)
    (hnn : 0 ≤ value.toRat) :
    STAmount.isRounded nt value = false ↔ STAmount.Representable nt value.toRat := by
  have hneg : value.negative_ = false := Number.negative_false_of_nonneg value hn hnn
  constructor
  · intro h
    by_cases hz : value.toRat = 0
    · exact Or.inl hz
    refine Or.inr ?_
    obtain ⟨st, n, hst, hnum, hval⟩ := STAmount.roundtrip_of_isRounded_false nt value hn h
    cases nt with
    | integral mv mo ms msh =>
      have hint : (NumericType.integral mv mo ms msh).isIntegral = true := rfl
      obtain ⟨hic, hty⟩ := STAmount.ofNumber_integral_canonical _ _ _ st hint hst
      have hsmall : st.mValue.toNat ≤ 2 ^ 63 - 1 := by
        by_cases hm0 : st.mValue = 0
        · rw [hm0]; decide
        · exact ((STAmount.ofNumber_exactCanonical _ value _ st hn hnn hst hm0).integralCanonical
            (show st.integral = true by unfold STAmount.integral; rw [hty]; rfl)).2
      obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_integral_small_exact st .to_nearest hic hsmall
      have hsnn : sn = n := Except.ok.inj (hsn.symm.trans hnum)
      -- the value is the stored magnitude
      have hst_val : value.toRat = (st.mValue.toNat : ℚ) := by
        have habs := STAmount.abs_toRat st
        rw [hic.offset_zero, zpow_zero, mul_one, ← hv, hsnn, hval, abs_of_nonneg hnn] at habs
        exact habs
      have hm0 : st.mValue ≠ 0 := by
        intro h0
        rw [h0] at hst_val
        exact hz (by rw [hst_val]; rfl)
      have hmax : st.mValue.toNat ≤ mv.toNat := by
        have := hic.in_range
        rw [hty] at this
        exact this
      exact ⟨STAmount.ofNumber_integral_maxOffset_nonneg _ value _ st hint hst hm0,
        st.mValue.toNat, hmax, hsmall, hst_val⟩
    | fractional =>
      have hm0 : st.mValue ≠ 0 := by
        intro h0
        have hfr : st.integral = false := by
          unfold STAmount.integral
          rw [STAmount.ofNumber_mNumericType _ _ _ st hst]
          rfl
        rw [STAmount.toNumber_zero_fractional st .to_nearest hfr h0, Except.ok.injEq] at hnum
        rw [← hnum, Number.toRat_zero] at hval
        exact hz hval.symm
      have hiou : st.IOUCanonical :=
        (STAmount.ofNumber_exactCanonical _ value _ st hn hnn hst hm0).iouCanonical
          (by unfold STAmount.integral; rw [STAmount.ofNumber_mNumericType _ _ _ st hst]; rfl)
      obtain ⟨sn, hsn, hv, -⟩ := STAmount.toNumber_iou_exact st .to_nearest hiou
      have hsnn : sn = n := Except.ok.inj (hsn.symm.trans hnum)
      have hst_val : value.toRat = (st.mValue.toNat : ℚ) * (10 : ℚ) ^ st.mOffset := by
        have habs := STAmount.abs_toRat st
        rw [← hv, hsnn, hval, abs_of_nonneg hnn] at habs
        exact habs
      exact ⟨st.mValue.toNat, st.mOffset, hiou.mant_lo, hiou.mant_hi, hiou.exp_lo, hiou.exp_hi,
        hst_val⟩
  · intro h
    by_cases hz : value.toRat = 0
    · rw [(Number.toRat_eq_zero_iff_eq_zero hn).mp hz]
      exact STAmount.isRounded_zero nt
    have hr := h.resolve_left hz
    cases nt with
    | integral mv mo ms msh =>
      obtain ⟨hmo, k, hkmax, hkcap, hk⟩ := hr
      have hden : value.toRat.den = 1 := by rw [hk]; rfl
      have hkcap' : (k : ℚ) ≤ 2 ^ 63 - 1 := by
        have : (k : ℚ) ≤ 9223372036854775807 := by exact_mod_cast (show k ≤ 9223372036854775807 by omega)
        linarith
      exact STAmount.isRounded_integral_eq_false _ value rfl hmo hn hnn hden
        (by rw [hk]; exact hkcap') (by rw [hk]; exact_mod_cast hkmax)
    | fractional =>
      obtain ⟨m, e, hmlo, hmhi, helo, hehi, hval⟩ := hr
      -- the normalized form of the value has mantissa `m · 1000` at exponent `e - 3`
      have hm64 : (m * 1000).toUInt64.toNat = m * 1000 :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      set w : Number := ⟨false, (m * 1000).toUInt64, e - 3⟩ with hw
      have hwnorm : w.isNormalized := by
        refine Or.inr ⟨?_, ?_, Or.inr ?_, ?_, ?_⟩
        · show largeRange.min ≤ (m * 1000).toUInt64
          rw [UInt64.le_iff_toNat_le, hm64]; simp [largeRange]; omega
        · show (m * 1000).toUInt64 ≤ largeRange.max
          rw [UInt64.le_iff_toNat_le, hm64]; simp [largeRange]; omega
        · show (m * 1000).toUInt64.toNat % 10 = 0
          rw [hm64]; omega
        · show minExponent ≤ e - 3
          unfold minExponent; omega
        · show e - 3 ≤ maxExponent
          unfold maxExponent; omega
      have hwval : w.toRat = value.toRat := by
        rw [Number.toRat_of_nonneg w rfl, hval]
        show ((m * 1000).toUInt64.toNat : ℚ) * (10 : ℚ) ^ (e - 3) = (m : ℚ) * (10 : ℚ) ^ e
        rw [hm64, zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0)]
        push_cast
        field_simp
      have hvw : value = w := Number.isNormalized.toRat_inj hn hwnorm hwval.symm
      have hmod : value.mantissa_.toNat % 1000 = 0 := by
        rw [hvw]; show (m * 1000).toUInt64.toNat % 1000 = 0; rw [hm64]; omega
      have hexp : value.exponent_ = e - 3 := by rw [hvw]
      have hm0 : value.mantissa_ ≠ 0 := fun h0 =>
        hz (Number.toRat_eq_zero_of_mantissa_zero value h0)
      have hok := STAmount.ofNumber_fractional_of_trailing_zeros value .to_nearest hn hm0 hneg hmod
        (by omega) (by omega)
      have hm3 : (value.mantissa_ / 10 / 10 / 10).toNat = value.mantissa_.toNat / 1000 :=
        m_div_thousand_toNat value.mantissa_
      have hmant : value.mantissa_.toNat = m * 1000 := by rw [hvw]; exact hm64
      have hiou : (⟨.fractional, value.mantissa_ / 10 / 10 / 10, value.exponent_ + 3, false⟩ :
          STAmount).IOUCanonical :=
        ⟨rfl, by show 10 ^ 15 ≤ (value.mantissa_ / 10 / 10 / 10).toNat; omega,
          by show (value.mantissa_ / 10 / 10 / 10).toNat < 10 ^ 16; omega,
          by show (-96 : ℤ) ≤ value.exponent_ + 3; omega, by show value.exponent_ + 3 ≤ 80; omega⟩
      refine STAmount.isRounded_false_of_exact _ value _ hn hok (Or.inl hiou) ?_
      rw [STAmount.toRat_of_nonneg _ rfl, hval]
      show ((value.mantissa_ / 10 / 10 / 10).toNat : ℚ) * (10 : ℚ) ^ (value.exponent_ + 3) = _
      rw [hm3, hmant, hexp, show e - 3 + 3 = e by ring, show m * 1000 / 1000 = m by omega]

/-- Rounding a value its asset stores exactly back to the asset keeps the value. -/
lemma STAmount.roundToNumericType_of_isRounded_false (nt : NumericType) (value r : Number)
    (hn : value.isNormalized) (h : STAmount.isRounded nt value = false)
    (hok : STAmount.roundToNumericType nt value .to_nearest = .ok r) : r.toRat = value.toRat := by
  unfold STAmount.isRounded STAmount.equalAfterNumberConvert at h
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt value .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    rw [hof] at hok h
    simp only [bind, Except.bind, pure, Except.pure] at h hok
    cases hsn : st.toNumber .to_nearest with
    | error e => rw [hsn] at h; exact absurd h (by simp)
    | ok n =>
      rw [hsn] at h hok
      obtain rfl := Except.ok.inj hok
      have heq : n.operator_eq value = true := by simpa using h
      exact (operator_eq_iff n value (STAmount.toNumber_isNormalized st _ n hsn) hn).mp heq

/-- A whole number of units below `10^16` at a scale in `[-81, 80]` is a value an IOU stores exactly. -/
lemma STAmount.representable_fractional_of_units (k : ℕ) (s : ℤ) (hk : k < 10 ^ 16)
    (hlo : (-81 : ℤ) ≤ s) (hhi : s ≤ 80) :
    STAmount.Representable .fractional ((k : ℚ) * (10 : ℚ) ^ s) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Or.inl (by simp)
  refine Or.inr ?_
  set d := Nat.log 10 k with hd
  have hdk : 10 ^ d ≤ k := Nat.pow_log_le_self 10 (by omega)
  have hkd : k < 10 ^ (d + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hd15 : d ≤ 15 := by
    by_contra h
    have : 10 ^ 16 ≤ 10 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨k * 10 ^ (15 - d), s - ((15 - d : ℕ) : ℤ), ?_, ?_, by omega, by omega, ?_⟩
  · calc 10 ^ 15 = 10 ^ d * 10 ^ (15 - d) := by rw [← pow_add]; congr 1; omega
      _ ≤ k * 10 ^ (15 - d) := Nat.mul_le_mul_right _ hdk
  · calc k * 10 ^ (15 - d) < 10 ^ (d + 1) * 10 ^ (15 - d) :=
          Nat.mul_lt_mul_of_pos_right hkd (by positivity)
      _ = 10 ^ 16 := by rw [← pow_add]; congr 1; omega
  · push_cast
    rw [zpow_sub₀ (by norm_num), zpow_natCast]
    field_simp

/-- An amount the asset stores is a normalized `Number`. -/
lemma STAmount.Representable.number {nt : NumericType} {x : ℚ} (h : STAmount.Representable nt x) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = x := by
  rcases h with rfl | h
  · exact ⟨Number.zero, Number.zero_isNormalized, Number.toRat_zero⟩
  cases nt with
  | integral mv mo ms msh =>
    obtain ⟨-, k, -, hk, rfl⟩ := h
    obtain ⟨w, hw, hwt⟩ := Number.exists_normalized_int_mul_pow (k : ℤ) 0
      ⟨by omega, by omega⟩ (by unfold minExponent maxExponent; omega)
    exact ⟨w, hw, by rw [hwt]; simp⟩
  | fractional =>
    obtain ⟨m, e, -, hm, he1, he2, rfl⟩ := h
    obtain ⟨w, hw, hwt⟩ := Number.exists_normalized_int_mul_pow (m : ℤ) e
      ⟨by omega, by omega⟩ (by unfold minExponent maxExponent; omega)
    exact ⟨w, hw, by rw [hwt]; push_cast; ring⟩

/-- An integral type stores a whole number exactly once rounding it to the type succeeds. -/
lemma STAmount.isRounded_eq_false_of_integral_round (nt : NumericType) (value r : Number) (hint : nt.isIntegral = true)
    (hn : value.isNormalized) (hnn : 0 ≤ value.toRat) (hden : value.toRat.den = 1)
    (hok : STAmount.roundToNumericType nt value .to_nearest = .ok r) :
    STAmount.isRounded nt value = false := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt value .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok st =>
    have hval := STAmount.ofNumber_integral_exact nt value .to_nearest st hint hn hden hof
    by_cases hm : st.mValue = 0
    · have h0 : value.toRat = 0 := by rw [← hval]; unfold STAmount.toRat; simp [hm]
      rw [(Number.toRat_eq_zero_iff_eq_zero hn).mp h0]
      exact STAmount.isRounded_zero nt
    · exact STAmount.isRounded_false_of_exact nt value st hn hof
        (STAmount.ofNumber_exactCanonical nt value .to_nearest st hn hnn hof hm) hval

/-- Rounding to an asset gives a value the asset stores exactly. -/
lemma STAmount.isRounded_roundToNumericType (nt : NumericType) (x y : Number) (hx : x.isNormalized)
    (h0 : 0 ≤ x.toRat) (hok : STAmount.roundToNumericType nt x .to_nearest = .ok y) :
    STAmount.isRounded nt y = false := by
  unfold STAmount.roundToNumericType at hok
  cases hof : STAmount.ofNumber nt x .to_nearest with
  | error e => rw [hof] at hok; exact absurd hok (by simp)
  | ok ret =>
    rw [hof] at hok
    simp only at hok
    have hty := STAmount.ofNumber_mNumericType _ _ _ ret hof
    have hret0 := STAmount.ofNumber_nonneg _ _ _ _ hx (Number.negative_false_of_nonneg x hx h0) hof
    -- a zero amount, integral or IOU, reads back as the exact zero
    by_cases hz : ret.mValue = 0
    · by_cases hint : nt.isIntegral = true
      · have hic := (STAmount.ofNumber_integral_canonical _ _ _ ret hint hof).1
        obtain ⟨hyv, hyn⟩ := STAmount.toNumber_exact_of ret y (Or.inr ⟨hic, by rw [hz]; decide⟩) hok
        have hy0 : y.toRat = 0 := by rw [hyv]; unfold STAmount.toRat; simp [hz]
        rw [(Number.toRat_eq_zero_iff_eq_zero hyn).mp hy0]
        exact STAmount.isRounded_zero nt
      · have hfr : ret.integral = false := by unfold STAmount.integral; rw [hty]; simpa using hint
        rw [STAmount.toNumber_zero_fractional ret .to_nearest hfr hz, Except.ok.injEq] at hok
        rw [← hok]
        exact STAmount.isRounded_zero nt
    have hc := STAmount.ofNumber_exactCanonical nt x .to_nearest ret hx h0 hof hz
    obtain ⟨hyv, hyn⟩ := STAmount.toNumber_exact_of ret y hc hok
    have habs := STAmount.abs_toRat ret
    rw [abs_of_nonneg hret0] at habs
    rw [STAmount.isRounded_eq_false_iff nt y hyn (by rw [hyv]; exact hret0), hyv, habs]
    refine Or.inr ?_
    cases hnt : nt with
    | integral mv mo ms msh =>
      have hint : nt.isIntegral = true := by rw [hnt]; rfl
      rw [hnt] at hty
      obtain ⟨hic, hsz⟩ := hc.resolve_left (fun hiou => by
        have := hiou.is_fractional; rw [hty] at this; exact absurd this (by simp))
      have hmo := STAmount.ofNumber_integral_maxOffset_nonneg nt x .to_nearest ret hint hof hz
      rw [hnt] at hmo
      have hin := hic.in_range
      rw [hty] at hin
      refine ⟨hmo, ret.mValue.toNat, hin, hsz, ?_⟩
      rw [hic.offset_zero, zpow_zero, mul_one]
    | fractional =>
      have hiou := hc.iouCanonical (by unfold STAmount.integral; rw [hty, hnt]; rfl)
      exact ⟨ret.mValue.toNat, ret.mOffset, hiou.mant_lo, hiou.mant_hi, hiou.exp_lo, hiou.exp_hi, rfl⟩

/-- A value on an exponent grid is a value the asset stores exactly. -/
lemma Number.isRounded_eq_false_of_isOnExponentGrid (value : Number) (exponent : Int) (nt : NumericType)
    (h : value.isOnExponentGrid exponent nt = .ok true) : STAmount.isRounded nt value = false := by
  unfold Number.isOnExponentGrid at h
  cases hr : STAmount.isRounded nt value
  · rfl
  · rw [hr] at h; simp [pure, Except.pure] at h

end XRPL.Model.Protocol
