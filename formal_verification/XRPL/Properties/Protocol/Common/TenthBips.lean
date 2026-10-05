import XRPL.Properties.Protocol.STAmount.Common.OfNumberRounding
import XRPL.Model.Protocol.TenthBips
import XRPL.Properties.Protocol.Common.Reduction
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable

/-! # Rates in tenth basis points

`tenthBipsOfValue` multiplies a value by a rate and divides by unity
(`100000` tenth basis points). These facts cover the rate itself, a zero value,
and the upward rounding of the product. -/

namespace XRPL.Model.Protocol

/-- With a zero value, `tenthBipsOfValue` gives zero. -/
lemma tenthBipsOfValue_zero (rate : TenthBips32) :
    tenthBipsOfValue Number.zero rate .upward = .ok Number.zero := by
  have hz : Number.zero.operator_eq Number.zero = true :=
    (operator_eq_iff _ _ Number.zero_isNormalized Number.zero_isNormalized).mpr rfl
  obtain ⟨r, hok, hval, hnorm⟩ := Number.from_rep_exact (100000 : Int64) 0 .to_nearest
    (by decide) (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  have hunit : kTenthBipsPerUnity.toNumber = r := by
    unfold kTenthBipsPerUnity TenthBips32.toNumber Number.ofInt64
    rw [show ((⟨100000⟩ : UInt32).toUInt64.toInt64) = (100000 : Int64) from by decide, hok]; rfl
  have hu : kTenthBipsPerUnity.toNumber.operator_eq Number.zero = false := by
    rw [hunit, Bool.eq_false_iff]
    intro h
    have := (operator_eq_iff _ _ hnorm Number.zero_isNormalized).mp h
    rw [hval, Number.toRat_zero] at this
    norm_num at this
    exact absurd this (by decide)
  simp [tenthBipsOfValue, Number.operator_mul, Number.operator_div, hz, hu, bind, Except.bind, pure,
    Except.pure]

/-- A rate converts to a normalized `Number` holding exactly its value. -/
lemma TenthBips32.toNumber_facts (rate : TenthBips32) :
    rate.toNumber.isNormalized ∧ rate.toNumber.toRat = rate.toNat := by
  have hlt : rate.toUInt64.toNat < 2 ^ 63 := by
    have := rate.toNat_lt_size
    have hs : UInt32.size = 2 ^ 32 := rfl
    simp only [UInt32.toNat_toUInt64]
    omega
  have hval := UInt64.toInt64_toInt_of_lt rate.toUInt64 hlt
  have hne : rate.toUInt64.toInt64 ≠ Int64.minValue := by
    intro h
    have h' := congrArg Int64.toInt h
    rw [hval, show Int64.minValue.toInt = -2 ^ 63 from by decide] at h'
    have := Int.natCast_nonneg rate.toUInt64.toNat
    linarith
  obtain ⟨r, hok, hv, hnorm⟩ := Number.from_rep_exact rate.toUInt64.toInt64 0 .to_nearest hne
    (by unfold minExponent; norm_num) (by unfold maxExponent; norm_num)
  have h : rate.toNumber = r := by
    unfold TenthBips32.toNumber Number.ofInt64
    rw [hok]
    rfl
  rw [h]
  refine ⟨hnorm, ?_⟩
  rw [hv, hval, UInt32.toNat_toUInt64]
  simp

/-- A rate's `Number` is not negative. -/
lemma TenthBips32.toNumber_nonneg (rate : TenthBips32) : 0 ≤ rate.toNumber.toRat := by
  rw [(TenthBips32.toNumber_facts rate).2]
  positivity

/-- An upward `tenthBipsOfValue` of a normalized nonnegative value is normalized
and not negative. It is zero, or the value times the rate divided by unity rounded
up twice. -/
lemma tenthBipsOfValue_upward_facts (d : Number) (rate : TenthBips32) (raw : Number)
    (hd : d.isNormalized) (h0 : 0 ≤ d.toRat)
    (hok : tenthBipsOfValue d rate .upward = .ok raw) :
    raw.isNormalized ∧ 0 ≤ raw.toRat := by
  have hrn := (TenthBips32.toNumber_facts rate).1
  have hr0 := TenthBips32.toNumber_nonneg rate
  have hun := (TenthBips32.toNumber_facts kTenthBipsPerUnity).1
  have hu0 := TenthBips32.toNumber_nonneg kTenthBipsPerUnity
  unfold tenthBipsOfValue at hok
  dsimp only at hok
  obtain ⟨p, hp, hok⟩ := bind_ok_peel _ _ _ hok
  have hpn := Number.operator_mul_isNormalized _ _ _ _ hd hrn hp
  -- a rounded-up result is zero, or at least its true value
  have hge (q : Number) (t : ℚ) (ht : 0 ≤ t)
      (hq : q.mantissa_ = 0 ∨ Number.RoundsToRepresentable q t .upward) : 0 ≤ q.toRat := by
    rcases hq with h0' | ⟨n, hn, hv⟩
    · exact le_of_eq (Number.toRat_eq_zero_of_mantissa_zero q h0').symm
    · rw [hv]
      exact le_trans ht (Number.le_upper _ _ hn)
  have hp0 : 0 ≤ p.toRat := hge p _ (mul_nonneg h0 hr0) (by
    by_cases h : p.mantissa_ = 0
    · exact Or.inl h
    · exact Or.inr (operator_mul_rounded_upward _ _ _ hd hrn hp h))
  refine ⟨Number.operator_div_isNormalized _ _ _ _ hpn hun hok, hge raw _ (div_nonneg hp0 hu0) ?_⟩
  by_cases h : raw.mantissa_ = 0
  · exact Or.inl h
  · exact Or.inr (operator_div_rounded_upward _ _ _ hpn hun hok h)

/-- **Upward `tenthBipsOfValue` keeps the order of nonnegative products.** The
multiplication by the rate and the division by unity both round up, and rounding
up keeps the order, so a larger value times rate never gives less. -/
lemma tenthBipsOfValue_upward_le (d d' : Number) (rate rate' : TenthBips32) (raw raw' : Number)
    (hd : d.isNormalized) (hd' : d'.isNormalized) (h0 : 0 ≤ d.toRat)
    (hprod : d.toRat * rate.toNumber.toRat ≤ d'.toRat * rate'.toNumber.toRat)
    (hok : tenthBipsOfValue d rate .upward = .ok raw)
    (hok' : tenthBipsOfValue d' rate' .upward = .ok raw') (hnz' : raw'.mantissa_ ≠ 0) :
    raw.toRat ≤ raw'.toRat := by
  have hrn := (TenthBips32.toNumber_facts rate).1
  have hr0 := TenthBips32.toNumber_nonneg rate
  have hrn' := (TenthBips32.toNumber_facts rate').1
  have hun := (TenthBips32.toNumber_facts kTenthBipsPerUnity).1
  have hu0 := TenthBips32.toNumber_nonneg kTenthBipsPerUnity
  unfold tenthBipsOfValue at hok hok'
  dsimp only at hok hok'
  obtain ⟨p, hp, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨p', hp', hok'⟩ := bind_ok_peel _ _ _ hok'
  have hpn := Number.operator_mul_isNormalized _ _ _ _ hd hrn hp
  have hpn' := Number.operator_mul_isNormalized _ _ _ _ hd' hrn' hp'
  have hrawn' := Number.operator_div_isNormalized _ _ _ _ hpn' hun hok'
  have hpr : p.mantissa_ = 0 ∨
      Number.RoundsToRepresentable p (d.toRat * rate.toNumber.toRat) .upward := by
    by_cases h : p.mantissa_ = 0
    · exact Or.inl h
    · exact Or.inr (operator_mul_rounded_upward _ _ _ hd hrn hp h)
  have hp0 : 0 ≤ p.toRat := by
    rcases hpr with h0' | ⟨n, hn, hv⟩
    · exact le_of_eq (Number.toRat_eq_zero_of_mantissa_zero p h0').symm
    · rw [hv]
      exact le_trans (mul_nonneg h0 hr0) (Number.le_upper _ _ hn)
  -- the larger side is nonzero all the way back
  have hp'0 : p'.mantissa_ ≠ 0 := (operator_div_operands_ne_zero hpn' hun hok' hnz').1
  have hple : p.toRat ≤ p'.toRat :=
    Number.toRat_le_of_rounds_upward p p' _ _ hpn' (mul_nonneg h0 hr0) hprod hpr
      (operator_mul_rounded_upward _ _ _ hd' hrn' hp' hp'0)
  have hrr : raw.mantissa_ = 0 ∨
      Number.RoundsToRepresentable raw (p.toRat / kTenthBipsPerUnity.toNumber.toRat) .upward := by
    by_cases h : raw.mantissa_ = 0
    · exact Or.inl h
    · exact Or.inr (operator_div_rounded_upward _ _ _ hpn hun hok h)
  exact Number.toRat_le_of_rounds_upward raw raw' _ _ hrawn' (div_nonneg hp0 hu0)
    (div_le_div_of_nonneg_right hple hu0) hrr
    (operator_div_rounded_upward _ _ _ hpn' hun hok' hnz')

end XRPL.Model.Protocol
