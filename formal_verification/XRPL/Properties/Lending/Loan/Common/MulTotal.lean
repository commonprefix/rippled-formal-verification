import XRPL.Properties.Protocol.Number.Totality

/-! # A product of two normalized numbers always computes below the top exponent

A product too small for a `Number` flushes to zero, so a multiply fails only when it overflows. -/

namespace XRPL.Model.Protocol

/-- The rounding step never raises the exponent above the source `e + 1` unless it flushes the mantissa to zero. -/
private lemma Guard.doRoundUp_output_exp_le_of_ne (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res) (hne : res.mantissa_ ≠ 0) :
    res.exponent_ ≤ e + 1 := by
  replace hok := Guard.doRoundUp_ok_spec hok
  unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec at hok
  dsimp only [Guard.doDropDigit] at hok
  unfold maxExponent minExponent at *
  split_ifs at hok <;>
    injection hok with hok' <;>
    subst hok' <;>
    (try simp only [] at *) <;>
    first | omega | exact absurd rfl hne

/-- Two normalized numbers multiply without error while their exponents sum to at most `maxExponent - 22`. -/
lemma Number.operator_mul_ok_of_exp_le (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized) (he_hi : x.exponent_ + y.exponent_ ≤ maxExponent - 22) :
    ∃ result, x.operator_mul y mode = .ok result := by
  by_cases hx0 : x.mantissa_ = 0
  · refine ⟨x, ?_⟩
    have := Number.eq_zero_of_mantissa_zero x hx hx0
    subst this
    rw [Number.operator_mul_eq_spec]
    unfold Number.operator_mulSpec
    rw [if_pos (by decide)]
    rfl
  by_cases hy0 : y.mantissa_ = 0
  · refine ⟨y, ?_⟩
    have := Number.eq_zero_of_mantissa_zero y hy hy0
    subst this
    rw [Number.operator_mul_eq_spec]
    unfold Number.operator_mulSpec
    simp only [Number.operator_eq_zero_false_of_mantissa_ne x hx0, Bool.false_eq_true, if_false]
    rw [if_pos (by decide)]
    rfl
  have hxm := (hx.mantissaBounds hx0).1
  have hym := (hy.mantissaBounds hy0).1
  have hxm_nat : (1000000000000000000 : ℕ) ≤ x.mantissa_.toNat := by
    have := UInt64.le_iff_toNat_le.mp hxm; rwa [largeRange_min_val] at this
  have hym_nat : (1000000000000000000 : ℕ) ≤ y.mantissa_.toNat := by
    have := UInt64.le_iff_toNat_le.mp hym; rwa [largeRange_min_val] at this
  rw [Number.operator_mul_eq_spec]
  unfold Number.operator_mulSpec
  rw [Number.operator_eq_zero_false_of_mantissa_ne x hx0]
  rw [Number.operator_eq_zero_false_of_mantissa_ne y hy0]
  simp only [Bool.false_eq_true, if_false]
  set zn := x.negative_ != y.negative_ with hzn_def
  set M := toUInt128 x.mantissa_ * toUInt128 y.mantissa_ with hM_def
  set ze := x.exponent_ + y.exponent_ with hze_def
  set g0 := if zn = true then Guard.new.set_negative else Guard.new with hg0_def
  set sd := scaleDown128Spec M ze g0 with hsd_def
  have hb := scaleDown128_output_bound M ze g0
  rw [← hsd_def] at hb
  obtain ⟨hzm_le, hze_lo, hze_hi⟩ := hb
  have hfit : x.mantissa_.toNat * y.mantissa_.toNat < 2 ^ 128 := by
    have hxlt : x.mantissa_.toNat < 2 ^ 64 := x.mantissa_.toNat_lt
    have hylt : y.mantissa_.toNat < 2 ^ 64 := y.mantissa_.toNat_lt
    calc x.mantissa_.toNat * y.mantissa_.toNat
        ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 128 := by norm_num
  have hMval : M.toNat = x.mantissa_.toNat * y.mantissa_.toNat := by
    rw [hM_def]; exact uint128_of_uint64_mul_toNat _ _ hfit
  have hMru : maxRepUp.toNat = 9223372036854775810 := rfl
  have hM_gt : maxRepUp.toNat < M.toNat := by
    rw [hMval, hMru]
    calc (9223372036854775810 : ℕ)
        < 1000000000000000000 * 1000000000000000000 := by norm_num
      _ ≤ x.mantissa_.toNat * y.mantissa_.toNat := Nat.mul_le_mul hxm_nat hym_nat
  have hzm_ge : (mantissaFloor : ℕ) ≤ sd.1.toNat := by
    have hlb := scaleDown128_lower_bound M ze g0 hM_gt
    rw [← hsd_def] at hlb
    simp only at hlb
    rw [hMru] at hlb
    omega
  obtain ⟨res, hres⟩ := Guard.doRoundUp_ok_of_exp_le sd.2.2 zn sd.1 sd.2.1
    largeRange.min largeRange.max mode .overflow largeRange_min_toNat_le (by omega)
  rw [hres]
  simp only []
  by_cases hrm : res.mantissa_ = 0
  · refine ⟨Number.zero, ?_⟩
    show doNormalize res.toNumber.negative_ res.toNumber.mantissa_ res.toNumber.exponent_
      largeRange.min largeRange.max mode = .ok Number.zero
    rw [doNormalize_eq_spec]
    all_goals try min_fit
    unfold doNormalizeSpec
    rw [if_pos (show (res.toNumber.mantissa_ == 0) = true from by
      show (res.mantissa_ == 0) = true; rw [beq_iff_eq]; exact hrm)]
  · have hexp_out : res.exponent_ ≤ sd.2.1 + 1 :=
      Guard.doRoundUp_output_exp_le_of_ne sd.2.2 zn sd.1 sd.2.1 largeRange.min largeRange.max mode
        .overflow res hres hrm
    obtain ⟨h_res_min, h_res_max, h_res_exp, h_res_mod⟩ :=
      doRoundUp_output_invariants_upTo_maxRepUp_anyMode sd.2.2 zn sd.1 sd.2.1 mode hzm_ge hzm_le
        .overflow res hres hrm
    have h_exp_le : res.exponent_ ≤ maxExponent := by omega
    have h_mru_exp : res.mantissa_.toNat > maxRepUp.toNat → res.exponent_ < maxExponent := by
      intro _; omega
    exact ⟨res.toNumber, doNormalize_id mode res.negative_ res.mantissa_ res.exponent_
      h_res_min h_res_max h_res_exp h_res_mod h_exp_le h_mru_exp⟩

end XRPL.Model.Protocol
