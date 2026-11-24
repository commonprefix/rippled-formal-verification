import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.Number.Common.Rounding.DivQuotient
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Add.Common.NoWrap
import XRPL.Properties.Protocol.Number.Add.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Mul.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Div.Common.SuccessCondition
import XRPL.Properties.Protocol.Number.Common.Rounding.TopGap

/-! # When the `Number` operations succeed

Success conditions of the four operations in each rounding mode, and the overflow error outside them. Add, subtract
and divide check for overflow before rounding (FV_M1_19), so their theorems carry `hrange` and a witness. -/

namespace XRPL.Model.Protocol

/-- `operator_neg` of a mantissa-zero `Number` is the canonical zero. -/
theorem Number.operator_neg_of_mantissa_zero (n : Number) (h : n.mantissa_ = 0) :
    n.operator_neg = Number.zero := by
  unfold Number.operator_neg
  rw [ite_eq_left (by rw [h]; rfl)]

/-- Adding the canonical zero on the right is the identity and never errors. -/
theorem Number.operator_add_zero_right (x : Number) (mode : rounding_mode) :
    x.operator_add Number.zero mode = .ok x := by
  unfold Number.operator_add
  rw [ite_eq_left (by decide : Number.zero.operator_eq Number.zero = true)]
  rfl

/-- Adding the canonical zero on the left returns the other operand and never errors. -/
theorem Number.operator_add_zero_left (y : Number) (mode : rounding_mode) :
    Number.zero.operator_add y mode = .ok y := by
  unfold Number.operator_add
  by_cases hy : y.operator_eq Number.zero = true
  · rw [ite_eq_left hy, (Number.operator_eq_iff_eq y Number.zero).mp hy]; rfl
  · rw [ite_eq_right hy, ite_eq_left (by decide : Number.zero.operator_eq Number.zero = true)]; rfl

/-- Subtracting a mantissa-zero `Number` returns the first operand unchanged, in every mode. -/
theorem Number.operator_sub_of_mantissa_zero (x y : Number) (mode : rounding_mode)
    (h : y.mantissa_ = 0) :
    x.operator_sub y mode = .ok x := by
  unfold Number.operator_sub
  rw [Number.operator_neg_of_mantissa_zero y h, Number.operator_add_zero_right]

/-- `operator_eq Number.zero` detects a zero mantissa, so a nonzero mantissa is not
equal to the canonical zero. -/
theorem Number.operator_eq_zero_false_of_mantissa_ne (n : Number) (h : n.mantissa_ ≠ 0) :
    n.operator_eq Number.zero = false := by
  unfold Number.operator_eq
  have : (n.mantissa_ == Number.zero.mantissa_) = false := by
    simp only [Number.zero]; exact beq_false_of_ne h
  simp [this]

/-- With a nonzero divisor, `operator_div` passes the divide-by-zero check and reduces to the
`doNormalize128` pipeline. -/
theorem Number.operator_div_of_divisor_ne (x y : Number) (mode : rounding_mode)
    (hy : y.mantissa_ ≠ 0) :
    x.operator_div y mode =
      (if x.operator_eq Number.zero then pure x
       else do
         let zn := x.negative_ != y.negative_
         let (zm128, ze, dropped) ←
           divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_
         doNormalize128 zn zm128 ze largeRange.min largeRange.max mode dropped) := by
  unfold Number.operator_div
  rw [Number.operator_eq_zero_false_of_mantissa_ne y hy, ite_eq_right Bool.false_ne_true]

/-- `doRoundUp` succeeds when the source exponent is at most `maxExponent - 1`, since the rounding step cannot
overflow. -/
theorem Guard.doRoundUp_ok_of_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (hmin : minM.toNat ≤ 10 ^ 18)
    (he : e + 1 ≤ maxExponent) :
    ∃ res, g.doRoundUp neg m e minM maxM mode loc = .ok res := by
  rw [Guard.doRoundUp_eq_spec _ _ _ _ _ _ _ hmin]
  unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec
  dsimp only [Guard.doDropDigit]
  unfold maxExponent minExponent at *
  split_ifs <;>
    first
      | exact ⟨_, rfl⟩
      | (exfalso; (try simp only [] at *); omega)

/-- From a source exponent `e ≥ minExponent`, a successful `doRoundUp` never raises the exponent above `e + 1`.
Only the carry drop-digit leg raises it, by one. -/
theorem Guard.doRoundUp_ok_output_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (he_lo : minExponent ≤ e)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res) :
    res.exponent_ ≤ e + 1 := by
  replace hok := Guard.doRoundUp_ok_spec hok
  unfold Guard.doRoundUpSpec Guard.bringIntoRangeSpec at hok
  dsimp only [Guard.doDropDigit] at hok
  unfold maxExponent minExponent at *
  split_ifs at hok <;>
    injection hok with hok' <;>
    subst hok' <;>
    (try simp only []) <;>
    omega

/-- `capAtMaxRep` succeeds below `maxExponent`. It either keeps the mantissa or drops one digit, raising the
exponent by one. -/
theorem doNormalize_capAtMaxRep_ok_of_exp (m : UInt64) (e : Int) (g : Guard)
    (he : e < maxExponent) :
    ∃ (m' : UInt64) (e' : Int) (g' : Guard),
      doNormalize_capAtMaxRep m e g = .ok (m', e', g') ∧ e' ≤ e + 1 := by
  unfold doNormalize_capAtMaxRep
  by_cases h : m > maxRepUp
  · rw [ite_eq_left h, ite_eq_right (show ¬ e ≥ maxExponent from not_le.mpr he)]
    exact ⟨(divu10 m).1, e + 1, g.push (divu10 m).2, rfl, le_refl _⟩
  · rw [ite_eq_right h]
    exact ⟨m, e, g, rfl, by omega⟩

/-- `scaleDown128Spec` runs some `k` steps: the output exponent is `e + k`, the output mantissa is `≤ maxRepUp`, and
`k ≥ 1` forces the input mantissa to be at least `9223372036854775811 * 10^(k - 1)`. -/
theorem scaleDown128_forward_exp_bound (M : UInt128) (e : Int) (g0 : Guard) :
    ∃ k : ℕ,
      (scaleDown128Spec M e g0).2.1 = e + (k : Int) ∧
      (scaleDown128Spec M e g0).1.toNat ≤ maxRepUp.toNat ∧
      (1 ≤ k → 9223372036854775811 * 10 ^ (k - 1) ≤ M.toNat) := by
  induction M, e, g0 using scaleDown128Spec.induct with
  | case1 M e g0 hcond d IH =>
    have hd_def : d = toUInt64 (M % 10) := rfl
    have h10_128 : (10 : UInt128).toNat = 10 := by decide
    have hM10_nat : (M / 10 : UInt128).toNat = M.toNat / 10 := by
      rw [BitVec.toNat_udiv, h10_128]
    have hM_gt : M.toNat > maxRepUp.toNat := by
      have := BitVec.lt_def.mp hcond
      rwa [toNat_toUInt128] at this
    have hunfold : scaleDown128Spec M e g0
        = scaleDown128Spec (M / 10) (e + 1) (g0.push d) := by
      conv_lhs => rw [scaleDown128Spec]
      simp [hcond, hd_def]
    rw [hunfold]
    obtain ⟨k, hek, hm, hinv⟩ := IH
    refine ⟨k + 1, ?_, hm, ?_⟩
    · rw [hek]; push_cast; ring
    · intro _
      have hkk : k + 1 - 1 = k := by omega
      rw [hkk]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [pow_zero, mul_one]
        have hR : maxRepUp.toNat = 9223372036854775810 := rfl
        omega
      · have hinv' := hinv hkpos
        rw [hM10_nat] at hinv'
        have hpow : (10 : ℕ) ^ k = 10 ^ (k - 1) * 10 := by
          conv_lhs => rw [show k = (k - 1) + 1 from by omega]
          rw [pow_succ]
        rw [hpow]
        set A := (10 : ℕ) ^ (k - 1)
        omega
  | case2 M e g0 hcond =>
    have hM_le : M.toNat ≤ maxRepUp.toNat := by
      have := BitVec.le_def.mp (BitVec.not_lt.mp hcond)
      rwa [toNat_toUInt128] at this
    have hfit : M.toNat < 2 ^ 64 := by
      have : maxRepUp.toNat < 2 ^ 64 := maxRepUp.toNat_lt; omega
    have hexit : scaleDown128Spec M e g0 = (toUInt64 M, e, g0) := by
      unfold scaleDown128Spec
      simp [hcond]
    rw [hexit]
    refine ⟨0, by simp, ?_, ?_⟩
    · show (toUInt64 M).toNat ≤ maxRepUp.toNat
      rw [toNat_toUInt64 hfit]; exact hM_le
    · intro h; exact absurd h (by omega)

/-- `scaleDown128Spec` returns a mantissa `≤ maxRepUp` and an exponent in `[e, e + 20]`, since a `UInt128` input
needs at most twenty digit drops. -/
theorem scaleDown128_output_bound (M : UInt128) (e : Int) (g0 : Guard) :
    (scaleDown128Spec M e g0).1.toNat ≤ maxRepUp.toNat ∧
    e ≤ (scaleDown128Spec M e g0).2.1 ∧
    (scaleDown128Spec M e g0).2.1 ≤ e + 20 := by
  obtain ⟨k, hek, hm, hinv⟩ := scaleDown128_forward_exp_bound M e g0
  have hk20 : k ≤ 20 := by
    by_contra hgt
    push Not at hgt
    have hk1 : 20 ≤ k - 1 := by omega
    have hpow : (10 : ℕ) ^ 20 ≤ 10 ^ (k - 1) :=
      Nat.pow_le_pow_right (by norm_num) hk1
    have hbound := hinv (by omega)
    have hMlt : M.toNat < 2 ^ 128 := M.isLt
    have h2 : (2 : ℕ) ^ 128 = 340282366920938463463374607431768211456 := by norm_num
    have h20 : (10 : ℕ) ^ 20 = 100000000000000000000 := by norm_num
    rw [h2] at hMlt
    rw [h20] at hpow
    set P := (10 : ℕ) ^ (k - 1)
    omega
  refine ⟨hm, ?_, ?_⟩
  · rw [hek]; omega
  · rw [hek]; omega

/-- `operator_mul` succeeds in every mode when both mantissas are at least `largeRange.min` and the exponent
sum `x.exponent_ + y.exponent_` lies in `[minExponent, maxExponent - 22]`. -/
theorem Number.operator_mul_ok_of_large_operands
    (x y : Number) (mode : rounding_mode)
    (hxm : largeRange.min ≤ x.mantissa_) (hym : largeRange.min ≤ y.mantissa_)
    (he_lo : minExponent ≤ x.exponent_ + y.exponent_)
    (he_hi : x.exponent_ + y.exponent_ ≤ maxExponent - 22) :
    ∃ result, x.operator_mul y mode = .ok result := by
  have hxm_nat : (1000000000000000000 : ℕ) ≤ x.mantissa_.toNat := by
    have := UInt64.le_iff_toNat_le.mp hxm; rwa [largeRange_min_val] at this
  have hym_nat : (1000000000000000000 : ℕ) ≤ y.mantissa_.toNat := by
    have := UInt64.le_iff_toNat_le.mp hym; rwa [largeRange_min_val] at this
  have hx : x.mantissa_ ≠ 0 := by intro h; rw [h] at hxm_nat; simp at hxm_nat
  have hy : y.mantissa_ ≠ 0 := by intro h; rw [h] at hym_nat; simp at hym_nat
  rw [Number.operator_mul_eq_spec]
  unfold Number.operator_mulSpec
  rw [Number.operator_eq_zero_false_of_mantissa_ne x hx]
  rw [Number.operator_eq_zero_false_of_mantissa_ne y hy]
  simp only [Bool.false_eq_true, ite_false]
  set zn := x.negative_ != y.negative_ with hzn_def
  set M := toUInt128 x.mantissa_ * toUInt128 y.mantissa_ with hM_def
  set ze := x.exponent_ + y.exponent_ with hze_def
  set g0 := if zn = true then Guard.new.set_negative else Guard.new with hg0_def
  set sd := scaleDown128Spec M ze g0 with hsd_def
  -- front-half loop output bounds (mantissa ≤ maxRepUp, exponent in [ze, ze+20])
  have hb := scaleDown128_output_bound M ze g0
  rw [← hsd_def] at hb
  obtain ⟨hzm_le, hze_lo, hze_hi⟩ := hb
  -- the UInt128 product equals the mantissa product and exceeds maxRepUp
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
  -- so the loop output mantissa lands at or above the floor
  have hzm_ge : (mantissaFloor : ℕ) ≤ sd.1.toNat := by
    have hlb := scaleDown128_lower_bound M ze g0 hM_gt
    rw [← hsd_def] at hlb
    simp only at hlb
    rw [hMru] at hlb
    omega
  -- the mid doRoundUp succeeds
  obtain ⟨res, hres⟩ := Guard.doRoundUp_ok_of_exp_le sd.2.2 zn sd.1 sd.2.1
    largeRange.min largeRange.max mode .overflow largeRange_min_toNat_le (by omega)
  rw [hres]
  simp only []
  have hexp_out : res.exponent_ ≤ sd.2.1 + 1 :=
    Guard.doRoundUp_ok_output_exp_le sd.2.2 zn sd.1 sd.2.1 largeRange.min largeRange.max mode
      .overflow res (by omega) hres
  -- the final normalize always succeeds: a flushed mantissa takes the zero branch, an
  -- in-range mantissa is returned unchanged by doNormalize_id
  by_cases hrm : res.mantissa_ = 0
  · refine ⟨Number.zero, ?_⟩
    show doNormalize res.toNumber.negative_ res.toNumber.mantissa_ res.toNumber.exponent_
      largeRange.min largeRange.max mode = .ok Number.zero
    rw [doNormalize_eq_spec]
    all_goals try min_fit
    unfold doNormalizeSpec
    rw [ite_eq_left (show (res.toNumber.mantissa_ == 0) = true from by
      show (res.mantissa_ == 0) = true; rw [beq_iff_eq]; exact hrm)]
  · obtain ⟨h_res_min, h_res_max, h_res_exp, h_res_mod⟩ :=
      doRoundUp_output_invariants_upTo_maxRepUp_anyMode sd.2.2 zn sd.1 sd.2.1 mode hzm_ge hzm_le
        .overflow res hres hrm
    have h_exp_le : res.exponent_ ≤ maxExponent := by omega
    have h_mru_exp : res.mantissa_.toNat > maxRepUp.toNat → res.exponent_ < maxExponent := by
      intro _; omega
    exact ⟨res.toNumber, doNormalize_id mode res.negative_ res.mantissa_ res.exponent_
      h_res_min h_res_max h_res_exp h_res_mod h_exp_le h_mru_exp⟩

/-- `operator_mul` succeeds in every mode on two normalized nonzero operands whose exponent sum lies in
`[minExponent, maxExponent - 22]`. -/
lemma Number.operator_mul_ok_of_normalized
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (he_lo : minExponent ≤ x.exponent_ + y.exponent_)
    (he_hi : x.exponent_ + y.exponent_ ≤ maxExponent - 22) :
    ∃ result, x.operator_mul y mode = .ok result :=
  Number.operator_mul_ok_of_large_operands x y mode
    (hx.mantissaBounds hx0).1 (hy.mantissaBounds hy0).1 he_lo he_hi

/-- `doNormalize128_scaleUpSpec` never raises the exponent, since it only multiplies the mantissa by 10 and
decrements the exponent. -/
theorem doNormalize128_scaleUp_exp_le (minMant : UInt64) (m : UInt128) (e : Int) :
    (doNormalize128_scaleUpSpec minMant m e).2 ≤ e := by
  induction m, e using doNormalize128_scaleUpSpec.induct (minMantissa := minMant) with
  | case1 m e hcond IH =>
    rw [show doNormalize128_scaleUpSpec minMant m e
        = doNormalize128_scaleUpSpec minMant (m * 10) (e - 1) from by
      rw [doNormalize128_scaleUpSpec.eq_def]
      simp only [ite_eq_left hcond]]
    omega
  | case2 m e hcond =>
    have h : doNormalize128_scaleUpSpec minMant m e = (m, e) := by
      rw [doNormalize128_scaleUpSpec.eq_def]; simp only [ite_eq_right hcond]
    rw [h]

/-- If the mantissa is below `(maxMantissa + 1) · 10^d` and `e + d ≤ maxExponent`, `doNormalize_scaleDown128Spec`
succeeds with an output exponent at most `e + d`. -/
theorem doNormalize_scaleDown128_ok_aux (d : ℕ) :
    ∀ (m : UInt128) (e : Int) (g : Guard),
      m.toNat < (largeRange.max.toNat + 1) * 10 ^ d →
      e + (d : Int) ≤ maxExponent →
      ∃ (m' : UInt128) (e' : Int) (g' : Guard),
        doNormalize_scaleDown128Spec largeRange.max m e g = .ok (m', e', g') ∧
        e' ≤ e + (d : Int) := by
  induction d with
  | zero =>
    intro m e g hm _he
    have hmle : m.toNat ≤ largeRange.max.toNat := by
      rw [pow_zero, mul_one] at hm; omega
    have hnotgt : ¬ m > toUInt128 largeRange.max := by
      rw [gt_iff_lt, BitVec.lt_def, toNat_toUInt128]; omega
    refine ⟨m, e, g, ?_, ?_⟩
    · rw [doNormalize_scaleDown128Spec.eq_def, dite_eq_right hnotgt]
    · simp
  | succ d IH =>
    intro m e g hm he
    by_cases hgt : m > toUInt128 largeRange.max
    · have hne : ¬ (e ≥ maxExponent) := by push_cast at he; omega
      have h10 : ((10 : UInt128)).toNat = 10 := by decide
      have hmdiv : (m / 10 : UInt128).toNat = m.toNat / 10 := by
        rw [BitVec.toNat_udiv, h10]
      have hm10 : (m / 10 : UInt128).toNat < (largeRange.max.toNat + 1) * 10 ^ d := by
        rw [hmdiv, largeRange_max_val]
        rw [largeRange_max_val, pow_succ] at hm
        omega
      have he10 : (e + 1) + (d : Int) ≤ maxExponent := by push_cast at he ⊢; omega
      obtain ⟨m', e', g', hok, hle⟩ :=
        IH (m / 10) (e + 1) (g.push (toUInt64 (m % 10))) hm10 he10
      refine ⟨m', e', g', ?_, ?_⟩
      · rw [doNormalize_scaleDown128Spec.eq_def, dite_eq_left hgt, ite_eq_right hne]; exact hok
      · push_cast at hle ⊢; omega
    · refine ⟨m, e, g, ?_, ?_⟩
      · rw [doNormalize_scaleDown128Spec.eq_def, dite_eq_right hgt]
      · push_cast; omega

/-- `doNormalize128` succeeds whenever the source exponent is at most `maxExponent - 22`, with no mantissa
bound and no lower exponent bound. -/
theorem doNormalize128_ok_of_exp (zn : Bool) (M : UInt128) (e : Int)
    (mode : rounding_mode) (sticky : Bool) (he : e + 22 ≤ maxExponent) :
    ∃ result, doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result := by
  by_cases hM0 : (M == 0) = true
  · exact ⟨Number.zero, by unfold doNormalize128; rw [ite_eq_left hM0]⟩
  · rw [doNormalize128_eq_spec]
    unfold doNormalize128Spec
    rw [ite_eq_right hM0]
    simp only []
    rcases hsu : doNormalize128_scaleUpSpec largeRange.min M e with ⟨M₁, e₁⟩
    simp only []
    have he₁ : e₁ ≤ e := by
      have h := doNormalize128_scaleUp_exp_le largeRange.min M e
      rw [hsu] at h; exact h
    set g₀ : Guard := (if sticky = true
        then (if zn then Guard.new.set_negative else Guard.new).set_sticky
        else (if zn then Guard.new.set_negative else Guard.new)) with hg₀_def
    have hmag : M₁.toNat < (largeRange.max.toNat + 1) * 10 ^ 20 := by
      calc M₁.toNat < 2 ^ 128 := M₁.isLt
        _ ≤ (largeRange.max.toNat + 1) * 10 ^ 20 := by rw [largeRange_max_val]; norm_num
    obtain ⟨m', e', g', hsd, hle'⟩ :=
      doNormalize_scaleDown128_ok_aux 20 M₁ e₁ g₀ hmag (by push_cast; omega)
    rw [hsd]
    simp only []
    by_cases hund : (e' < minExponent || m' < toUInt128 largeRange.min) = true
    · rw [ite_eq_left hund]; exact ⟨Number.zero, rfl⟩
    · rw [ite_eq_right hund]
      obtain ⟨m'', e'', g'', hcap, hle''⟩ :=
        doNormalize_capAtMaxRep_ok_of_exp (toUInt64 m') e' g' (by push_cast at hle'; omega)
      rw [hcap]
      simp only []
      obtain ⟨res, hru⟩ :=
        Guard.doRoundUp_ok_of_exp_le g'' zn m'' e'' largeRange.min largeRange.max mode
          .normalize2 largeRange_min_toNat_le (by push_cast at hle' hle''; omega)
      rw [hru]
      exact ⟨res.toNumber, rfl⟩

/-- `operator_div` succeeds in every mode on two normalized nonzero operands with
`x.exponent_ - y.exponent_ ≤ maxExponent - 5`, which leaves `doNormalize128` the headroom it needs. -/
lemma Number.operator_div_ok_of_normalized
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (he : x.exponent_ - y.exponent_ ≤ maxExponent - 5) :
    ∃ result, x.operator_div y mode = .ok result := by
  have hxb := hx.mantissaBounds hx0
  have hyb := hy.mantissaBounds hy0
  obtain ⟨zmq, zeq, drp, N, r, hdq, htail⟩ :=
    divQuotient128_correct x.mantissa_ y.mantissa_ x.exponent_ y.exponent_
      (Number.mantissa_toNat_pos_of_bounds hxb)
      (Number.mantissa_toNat_pos_of_bounds hyb)
      (UInt64.le_iff_toNat_le.mp hxb.2)
      (UInt64.le_iff_toNat_le.mp hyb.2)
      (UInt64.le_iff_toNat_le.mp hyb.1)
  obtain ⟨hN, -, -, hzeq, -, -⟩ := htail
  have hze : zeq + 22 ≤ maxExponent := by rcases hN with rfl | rfl <;> omega
  have hxeq : x.operator_eq Number.zero = false :=
    Number.operator_eq_zero_false_of_mantissa_ne x hx0
  rw [Number.operator_div_of_divisor_ne x y mode hy0, hxeq, ite_eq_right Bool.false_ne_true, hdq, ok_bind]
  exact doNormalize128_ok_of_exp (x.negative_ != y.negative_) zmq zeq mode drp hze

/-- The `Number` exponent of a nonzero normalized source sits at or above `minExponent`. -/
lemma Number.exponent_ge_min (n : Number) (hn : n.isNormalized) (hn0 : n.mantissa_ ≠ 0) :
    minExponent ≤ n.exponent_ := by
  rcases hn with hz | ⟨_, _, _, hemin, _⟩
  · exfalso; apply hn0; rw [hz]; rfl
  · exact hemin

/-- A normalized Number whose exponent is at least 3 below `maxExponent` is at most `10^16 · 10^maxExponent` in size. -/
private lemma Number.abs_toRat_le_of_exp (x : Number) (hx : x.isNormalized) (hxe : x.exponent_ + 3 ≤ maxExponent) :
    |x.toRat| ≤ 10 ^ 16 * (10 : ℚ) ^ (maxExponent : ℤ) := by
  rw [abs_toRat_eq]
  have hm : (x.mantissa_.toNat : ℚ) ≤ 10 ^ 19 := by
    rcases hx with hz | ⟨_, hhi, _⟩
    · rw [hz]; norm_num [Number.zero]
    · have := (mantissaBounds_nat_of ⟨by assumption, hhi⟩).2
      exact_mod_cast this.le
  have hp : (10 : ℚ) ^ x.exponent_ * 10 ^ (3 : ℤ) ≤ 10 ^ (maxExponent : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num) hxe
  have hpos : (0 : ℚ) < 10 ^ x.exponent_ := zpow_pos (by norm_num) _
  norm_num at hp
  nlinarith

/-- `operator_add` succeeds on two normalized operands with exponent headroom. Either operand may be zero, and the
signs may differ. -/
lemma Number.operator_add_ok_of_exp (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxe : x.exponent_ + 22 ≤ maxExponent) (hye : y.exponent_ + 22 ≤ maxExponent) :
    ∃ result, x.operator_add y mode = .ok result := by
  by_cases hy0 : y.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero y hy hy0]
    exact ⟨x, Number.operator_add_zero_right x mode⟩
  by_cases hx0 : x.mantissa_ = 0
  · rw [Number.eq_zero_of_mantissa_zero x hx hx0]
    unfold Number.operator_add
    rw [Number.operator_eq_zero_false_of_mantissa_ne y hy0, ite_eq_right Bool.false_ne_true,
      ite_eq_left (by decide)]
    exact ⟨y, rfl⟩
  refine (Number.operator_add_ok_iff_proof x y mode hx hy hx0 hy0).mpr ?_
  have hbx := Number.abs_toRat_le_of_exp x hx (by omega)
  have hby := Number.abs_toRat_le_of_exp y hy (by omega)
  have hT : (0 : ℚ) < 10 ^ (maxExponent : ℤ) := zpow_pos (by norm_num) _
  calc |x.toRat + y.toRat| ≤ |x.toRat| + |y.toRat| := abs_add_le _ _
    _ < 9223372036854775811 * (10 : ℚ) ^ (maxExponent : ℤ) := by nlinarith

/-- `operator_sub` succeeds on two normalized operands with exponent headroom. Either operand may be zero, and the
signs may differ. -/
lemma Number.operator_sub_ok_of_exp (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxe : x.exponent_ + 22 ≤ maxExponent) (hye : y.exponent_ + 22 ≤ maxExponent) :
    ∃ result, x.operator_sub y mode = .ok result := by
  unfold Number.operator_sub
  apply Number.operator_add_ok_of_exp x y.operator_neg mode hx
    (Number.operator_neg_isNormalized y hy) hxe
  unfold Number.operator_neg
  split_ifs
  · show (-2147483648 : Int) + 22 ≤ maxExponent
    unfold maxExponent; norm_num
  · exact hye

/-- `to_nearest` `x + y` succeeds exactly when the exact sum is below `Number.top_plus_five` in size. `hrange` leaves
out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat + y.toRat| < Number.top_plus_one ∨ Number.top_plus_five ≤ |x.toRat + y.toRat|) :
    (∃ result, x.operator_add y .to_nearest = .ok result) ↔
      |x.toRat + y.toRat| < Number.top_plus_five :=
  (Number.operator_add_ok_iff_proof x y .to_nearest hx hy hx0 hy0).trans (topGap_to_nearest_agree_iff.mpr hrange)

/-- A sum left out by `hrange`: it is below `Number.top_plus_five` in size, and `to_nearest` `x + y` fails with an
overflow error. -/
theorem Number.operator_add_ok_iff_to_nearest_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat + y.toRat| < Number.top_plus_five ∧
      ∃ err,
        x.operator_add y .to_nearest = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.add_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat + y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, by rw [habs]; linarith,
    Number.operator_add_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `towards_zero` `x + y` succeeds exactly when the exact sum is below `Number.top_plus_ten` in size. `hrange` leaves
out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat + y.toRat| < Number.top_plus_one ∨ Number.top_plus_ten ≤ |x.toRat + y.toRat|) :
    (∃ result, x.operator_add y .towards_zero = .ok result) ↔
      |x.toRat + y.toRat| < Number.top_plus_ten :=
  (Number.operator_add_ok_iff_proof x y .towards_zero hx hy hx0 hy0).trans (topGap_towards_zero_agree_iff.mpr hrange)

/-- A sum left out by `hrange`: it is below `Number.top_plus_ten` in size, and `towards_zero` `x + y` fails with an
overflow error. -/
theorem Number.operator_add_ok_iff_towards_zero_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat + y.toRat| < Number.top_plus_ten ∧
      ∃ err,
        x.operator_add y .towards_zero = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.add_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat + y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, by rw [habs]; linarith,
    Number.operator_add_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `downward` `x + y` succeeds exactly when the exact sum is at least `-Number.top` and below `Number.top_plus_ten`.
`hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat + y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat + y.toRat) ∧
      (x.toRat + y.toRat < Number.top_plus_one ∨ Number.top_plus_ten ≤ x.toRat + y.toRat)) :
    (∃ result, x.operator_add y .downward = .ok result) ↔
      -Number.top ≤ x.toRat + y.toRat ∧ x.toRat + y.toRat < Number.top_plus_ten :=
  (Number.operator_add_ok_iff_proof x y .downward hx hy hx0 hy0).trans (topGap_downward_agree_iff.mpr hrange)

/-- A sum left out by `hrange`: it is at least `-Number.top` and below `Number.top_plus_ten`, and `downward` `x + y`
fails with an overflow error. -/
theorem Number.operator_add_ok_iff_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top ≤ x.toRat + y.toRat ∧ x.toRat + y.toRat < Number.top_plus_ten) ∧
      ∃ err,
        x.operator_add y .downward = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.add_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat + y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, ⟨by linarith, by linarith⟩,
    Number.operator_add_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `upward` `x + y` succeeds exactly when the exact sum is above `-Number.top_plus_ten` and at most `Number.top`.
`hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat + y.toRat ≤ -Number.top_plus_ten ∨ -Number.top_plus_one < x.toRat + y.toRat) ∧
      (x.toRat + y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat + y.toRat)) :
    (∃ result, x.operator_add y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat + y.toRat ∧ x.toRat + y.toRat ≤ Number.top :=
  (Number.operator_add_ok_iff_proof x y .upward hx hy hx0 hy0).trans (topGap_upward_agree_iff.mpr hrange)

/-- A sum left out by `hrange`: it is above `-Number.top_plus_ten` and at most `Number.top`, and `upward` `x + y` fails
with an overflow error. -/
theorem Number.operator_add_ok_iff_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top_plus_ten < x.toRat + y.toRat ∧ x.toRat + y.toRat ≤ Number.top) ∧
      ∃ err,
        x.operator_add y .upward = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.add_topGap_mid_neg
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonpos (show x.toRat + y.toRat ≤ 0 by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, ⟨by linarith, by linarith⟩,
    Number.operator_add_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `to_nearest` `x - y` succeeds exactly when the exact difference is below `Number.top_plus_five` in size. `hrange`
leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat - y.toRat| < Number.top_plus_one ∨ Number.top_plus_five ≤ |x.toRat - y.toRat|) :
    (∃ result, x.operator_sub y .to_nearest = .ok result) ↔
      |x.toRat - y.toRat| < Number.top_plus_five :=
  (Number.operator_sub_ok_iff_proof x y .to_nearest hx hy hx0 hy0).trans (topGap_to_nearest_agree_iff.mpr hrange)

/-- A difference left out by `hrange`: it is below `Number.top_plus_five` in size, and `to_nearest` `x - y` fails with
an overflow error. -/
theorem Number.operator_sub_ok_iff_to_nearest_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat - y.toRat| < Number.top_plus_five ∧
      ∃ err,
        x.operator_sub y .to_nearest = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.sub_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat - y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, by rw [habs]; linarith,
    Number.operator_sub_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `towards_zero` `x - y` succeeds exactly when the exact difference is below `Number.top_plus_ten` in size. `hrange`
leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat - y.toRat| < Number.top_plus_one ∨ Number.top_plus_ten ≤ |x.toRat - y.toRat|) :
    (∃ result, x.operator_sub y .towards_zero = .ok result) ↔
      |x.toRat - y.toRat| < Number.top_plus_ten :=
  (Number.operator_sub_ok_iff_proof x y .towards_zero hx hy hx0 hy0).trans (topGap_towards_zero_agree_iff.mpr hrange)

/-- A difference left out by `hrange`: it is below `Number.top_plus_ten` in size, and `towards_zero` `x - y` fails with
an overflow error. -/
theorem Number.operator_sub_ok_iff_towards_zero_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat - y.toRat| < Number.top_plus_ten ∧
      ∃ err,
        x.operator_sub y .towards_zero = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.sub_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat - y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, by rw [habs]; linarith,
    Number.operator_sub_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `downward` `x - y` succeeds exactly when the exact difference is at least `-Number.top` and below
`Number.top_plus_ten`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat - y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat - y.toRat) ∧
      (x.toRat - y.toRat < Number.top_plus_one ∨ Number.top_plus_ten ≤ x.toRat - y.toRat)) :
    (∃ result, x.operator_sub y .downward = .ok result) ↔
      -Number.top ≤ x.toRat - y.toRat ∧ x.toRat - y.toRat < Number.top_plus_ten :=
  (Number.operator_sub_ok_iff_proof x y .downward hx hy hx0 hy0).trans (topGap_downward_agree_iff.mpr hrange)

/-- A difference left out by `hrange`: it is at least `-Number.top` and below `Number.top_plus_ten`, and `downward`
`x - y` fails with an overflow error. -/
theorem Number.operator_sub_ok_iff_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top ≤ x.toRat - y.toRat ∧ x.toRat - y.toRat < Number.top_plus_ten) ∧
      ∃ err,
        x.operator_sub y .downward = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.sub_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat - y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, ⟨by linarith, by linarith⟩,
    Number.operator_sub_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `upward` `x - y` succeeds exactly when the exact difference is above `-Number.top_plus_ten` and at most
`Number.top`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat - y.toRat ≤ -Number.top_plus_ten ∨ -Number.top_plus_one < x.toRat - y.toRat) ∧
      (x.toRat - y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat - y.toRat)) :
    (∃ result, x.operator_sub y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat - y.toRat ∧ x.toRat - y.toRat ≤ Number.top :=
  (Number.operator_sub_ok_iff_proof x y .upward hx hy hx0 hy0).trans (topGap_upward_agree_iff.mpr hrange)

/-- A difference left out by `hrange`: it is above `-Number.top_plus_ten` and at most `Number.top`, and `upward` `x - y`
fails with an overflow error. -/
theorem Number.operator_sub_ok_iff_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top_plus_ten < x.toRat - y.toRat ∧ x.toRat - y.toRat ≤ Number.top) ∧
      ∃ err,
        x.operator_sub y .upward = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.sub_topGap_mid_neg
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonpos (show x.toRat - y.toRat ≤ 0 by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, ⟨by linarith, by linarith⟩,
    Number.operator_sub_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `to_nearest` `x / y` succeeds exactly when the exact quotient is below `Number.top_plus_five` in size. `hrange`
leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat / y.toRat| < Number.top_plus_one ∨ Number.top_plus_five ≤ |x.toRat / y.toRat|) :
    (∃ result, x.operator_div y .to_nearest = .ok result) ↔
      |x.toRat / y.toRat| < Number.top_plus_five :=
  (Number.operator_div_ok_iff_proof x y .to_nearest hx hy hx0 hy0).trans (topGap_to_nearest_agree_iff.mpr hrange)

/-- A quotient left out by `hrange`: it is below `Number.top_plus_five` in size, and `to_nearest` `x / y` fails with an
overflow error. -/
theorem Number.operator_div_ok_iff_to_nearest_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat / y.toRat| < Number.top_plus_five ∧
      ∃ err,
        x.operator_div y .to_nearest = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.div_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat / y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, by rw [habs]; linarith,
    Number.operator_div_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `towards_zero` `x / y` succeeds exactly when the exact quotient is below `Number.top_plus_ten` in size. `hrange`
leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : |x.toRat / y.toRat| < Number.top_plus_one ∨ Number.top_plus_ten ≤ |x.toRat / y.toRat|) :
    (∃ result, x.operator_div y .towards_zero = .ok result) ↔
      |x.toRat / y.toRat| < Number.top_plus_ten :=
  (Number.operator_div_ok_iff_proof x y .towards_zero hx hy hx0 hy0).trans (topGap_towards_zero_agree_iff.mpr hrange)

/-- A quotient left out by `hrange`: it is below `Number.top_plus_ten` in size, and `towards_zero` `x / y` fails with an
overflow error. -/
theorem Number.operator_div_ok_iff_towards_zero_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      |x.toRat / y.toRat| < Number.top_plus_ten ∧
      ∃ err,
        x.operator_div y .towards_zero = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.div_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat / y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, by rw [habs]; linarith,
    Number.operator_div_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `downward` `x / y` succeeds exactly when the exact quotient is at least `-Number.top` and below
`Number.top_plus_ten`. `hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat / y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat / y.toRat) ∧
      (x.toRat / y.toRat < Number.top_plus_one ∨ Number.top_plus_ten ≤ x.toRat / y.toRat)) :
    (∃ result, x.operator_div y .downward = .ok result) ↔
      -Number.top ≤ x.toRat / y.toRat ∧ x.toRat / y.toRat < Number.top_plus_ten :=
  (Number.operator_div_ok_iff_proof x y .downward hx hy hx0 hy0).trans (topGap_downward_agree_iff.mpr hrange)

/-- A quotient left out by `hrange`: it is at least `-Number.top` and below `Number.top_plus_ten`, and `downward`
`x / y` fails with an overflow error. -/
theorem Number.operator_div_ok_iff_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top ≤ x.toRat / y.toRat ∧ x.toRat / y.toRat < Number.top_plus_ten) ∧
      ∃ err,
        x.operator_div y .downward = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.div_topGap_mid_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat / y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, ⟨by linarith, by linarith⟩,
    Number.operator_div_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- `upward` `x / y` succeeds exactly when the exact quotient is above `-Number.top_plus_ten` and at most `Number.top`.
`hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : (x.toRat / y.toRat ≤ -Number.top_plus_ten ∨ -Number.top_plus_one < x.toRat / y.toRat) ∧
      (x.toRat / y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat / y.toRat)) :
    (∃ result, x.operator_div y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat / y.toRat ∧ x.toRat / y.toRat ≤ Number.top :=
  (Number.operator_div_ok_iff_proof x y .upward hx hy hx0 hy0).trans (topGap_upward_agree_iff.mpr hrange)

/-- A quotient left out by `hrange`: it is above `-Number.top_plus_ten` and at most `Number.top`, and `upward` `x / y`
fails with an overflow error. -/
theorem Number.operator_div_ok_iff_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      (-Number.top_plus_ten < x.toRat / y.toRat ∧ x.toRat / y.toRat ≤ Number.top) ∧
      ∃ err,
        x.operator_div y .upward = .error err ∧
        isOverflow err = true := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.div_topGap_mid_neg
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonpos (show x.toRat / y.toRat ≤ 0 by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, ⟨by linarith, by linarith⟩,
    Number.operator_div_overflow_proof x y _ hx hy hx0 hy0
      (by show Number.top_plus_one ≤ _; rw [habs]; linarith)⟩

/-- In `to_nearest`, `x * y` succeeds exactly when the exact product is below `Number.top_plus_five` in size. -/
theorem Number.operator_mul_ok_iff_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .to_nearest = .ok result) ↔
      |x.toRat * y.toRat| < Number.top_plus_five :=
  Number.operator_mul_ok_iff_to_nearest_proof x y hx hy hx0 hy0

/-- In `towards_zero`, `x * y` succeeds exactly when the exact product is below `Number.top_plus_ten` in size. -/
theorem Number.operator_mul_ok_iff_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .towards_zero = .ok result) ↔
      |x.toRat * y.toRat| < Number.top_plus_ten :=
  Number.operator_mul_ok_iff_towards_zero_proof x y hx hy hx0 hy0

/-- In `downward`, `x * y` succeeds exactly when the exact product is at least `-Number.top` and below
`Number.top_plus_ten`. -/
theorem Number.operator_mul_ok_iff_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .downward = .ok result) ↔
      -Number.top ≤ x.toRat * y.toRat ∧ x.toRat * y.toRat < Number.top_plus_ten :=
  Number.operator_mul_ok_iff_downward_proof x y hx hy hx0 hy0

/-- In `upward`, `x * y` succeeds exactly when the exact product is above `-Number.top_plus_ten` and at most
`Number.top`. -/
theorem Number.operator_mul_ok_iff_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0) :
    (∃ result, x.operator_mul y .upward = .ok result) ↔
      -Number.top_plus_ten < x.toRat * y.toRat ∧ x.toRat * y.toRat ≤ Number.top :=
  Number.operator_mul_ok_iff_upward_proof x y hx hy hx0 hy0

/-- In `to_nearest`, `x + y` fails with an overflow error when the exact sum is at least `Number.top_plus_five` in size.
-/
theorem Number.operator_add_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat + y.toRat|) :
    ∃ err, x.operator_add y .to_nearest = .error err ∧ isOverflow err = true :=
  Number.operator_add_overflow_proof x y .to_nearest hx hy hx0 hy0 (topGap_overflow_to_nearest h)

/-- In `towards_zero`, `x + y` fails with an overflow error when the exact sum is at least `Number.top_plus_ten` in
size. -/
theorem Number.operator_add_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat + y.toRat|) :
    ∃ err, x.operator_add y .towards_zero = .error err ∧ isOverflow err = true :=
  Number.operator_add_overflow_proof x y .towards_zero hx hy hx0 hy0 (topGap_overflow_towards_zero h)

/-- `downward` `x + y` fails with an overflow error when the exact sum is below `-Number.top` or at least
`Number.top_plus_ten`. `hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat + y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat + y.toRat)
    (h : x.toRat + y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat + y.toRat) :
    ∃ err, x.operator_add y .downward = .error err ∧ isOverflow err = true :=
  Number.operator_add_overflow_proof x y .downward hx hy hx0 hy0
    (topGap_overflow_downward_iff.mpr hrange h)

/-- A sum left out by `hrange`: it is below `-Number.top`, and `downward` `x + y` returns a result. -/
theorem Number.operator_add_overflow_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      x.toRat + y.toRat < -Number.top ∧
      ∃ result,
        x.operator_add y .downward = .ok result := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.add_topGap_low_neg
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonpos (show x.toRat + y.toRat ≤ 0 by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, hhi,
    (Number.operator_add_ok_iff_proof x y _ hx hy hx0 hy0).mpr
      (by show _ < Number.top_plus_one; rw [habs]; linarith)⟩

/-- `upward` `x + y` fails with an overflow error when the exact sum is at most `-Number.top_plus_ten` or above
`Number.top`. `hrange` leaves out the sums where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_add_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat + y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat + y.toRat)
    (h : x.toRat + y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat + y.toRat) :
    ∃ err, x.operator_add y .upward = .error err ∧ isOverflow err = true :=
  Number.operator_add_overflow_proof x y .upward hx hy hx0 hy0
    (topGap_overflow_upward_iff.mpr hrange h)

/-- A sum left out by `hrange`: it is above `Number.top`, and `upward` `x + y` returns a result. -/
theorem Number.operator_add_overflow_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat + y.toRat ∧
      ∃ result,
        x.operator_add y .upward = .ok result := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.add_topGap_low_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat + y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, hlo,
    (Number.operator_add_ok_iff_proof x y _ hx hy hx0 hy0).mpr
      (by show _ < Number.top_plus_one; rw [habs]; linarith)⟩

/-- In `to_nearest`, `x - y` fails with an overflow error when the exact difference is at least `Number.top_plus_five`
in size. -/
theorem Number.operator_sub_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat - y.toRat|) :
    ∃ err, x.operator_sub y .to_nearest = .error err ∧ isOverflow err = true :=
  Number.operator_sub_overflow_proof x y .to_nearest hx hy hx0 hy0 (topGap_overflow_to_nearest h)

/-- In `towards_zero`, `x - y` fails with an overflow error when the exact difference is at least `Number.top_plus_ten`
in size. -/
theorem Number.operator_sub_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat - y.toRat|) :
    ∃ err, x.operator_sub y .towards_zero = .error err ∧ isOverflow err = true :=
  Number.operator_sub_overflow_proof x y .towards_zero hx hy hx0 hy0 (topGap_overflow_towards_zero h)

/-- `downward` `x - y` fails with an overflow error when the exact difference is below `-Number.top` or at least
`Number.top_plus_ten`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat - y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat - y.toRat)
    (h : x.toRat - y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat - y.toRat) :
    ∃ err, x.operator_sub y .downward = .error err ∧ isOverflow err = true :=
  Number.operator_sub_overflow_proof x y .downward hx hy hx0 hy0
    (topGap_overflow_downward_iff.mpr hrange h)

/-- A difference left out by `hrange`: it is below `-Number.top`, and `downward` `x - y` returns a result. -/
theorem Number.operator_sub_overflow_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      x.toRat - y.toRat < -Number.top ∧
      ∃ result,
        x.operator_sub y .downward = .ok result := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.sub_topGap_low_neg
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonpos (show x.toRat - y.toRat ≤ 0 by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, hhi,
    (Number.operator_sub_ok_iff_proof x y _ hx hy hx0 hy0).mpr
      (by show _ < Number.top_plus_one; rw [habs]; linarith)⟩

/-- `upward` `x - y` fails with an overflow error when the exact difference is at most `-Number.top_plus_ten` or above
`Number.top`. `hrange` leaves out the differences where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_sub_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat - y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat - y.toRat)
    (h : x.toRat - y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat - y.toRat) :
    ∃ err, x.operator_sub y .upward = .error err ∧ isOverflow err = true :=
  Number.operator_sub_overflow_proof x y .upward hx hy hx0 hy0
    (topGap_overflow_upward_iff.mpr hrange h)

/-- A difference left out by `hrange`: it is above `Number.top`, and `upward` `x - y` returns a result. -/
theorem Number.operator_sub_overflow_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat - y.toRat ∧
      ∃ result,
        x.operator_sub y .upward = .ok result := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.sub_topGap_low_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat - y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, hlo,
    (Number.operator_sub_ok_iff_proof x y _ hx hy hx0 hy0).mpr
      (by show _ < Number.top_plus_one; rw [habs]; linarith)⟩

/-- In `to_nearest`, `x / y` fails with an overflow error when the exact quotient is at least `Number.top_plus_five` in
size. -/
theorem Number.operator_div_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat / y.toRat|) :
    ∃ err, x.operator_div y .to_nearest = .error err ∧ isOverflow err = true :=
  Number.operator_div_overflow_proof x y .to_nearest hx hy hx0 hy0 (topGap_overflow_to_nearest h)

/-- In `towards_zero`, `x / y` fails with an overflow error when the exact quotient is at least `Number.top_plus_ten` in
size. -/
theorem Number.operator_div_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat / y.toRat|) :
    ∃ err, x.operator_div y .towards_zero = .error err ∧ isOverflow err = true :=
  Number.operator_div_overflow_proof x y .towards_zero hx hy hx0 hy0 (topGap_overflow_towards_zero h)

/-- `downward` `x / y` fails with an overflow error when the exact quotient is below `-Number.top` or at least
`Number.top_plus_ten`. `hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat / y.toRat ≤ -Number.top_plus_one ∨ -Number.top ≤ x.toRat / y.toRat)
    (h : x.toRat / y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat / y.toRat) :
    ∃ err, x.operator_div y .downward = .error err ∧ isOverflow err = true :=
  Number.operator_div_overflow_proof x y .downward hx hy hx0 hy0
    (topGap_overflow_downward_iff.mpr hrange h)

/-- A quotient left out by `hrange`: it is below `-Number.top`, and `downward` `x / y` returns a result. -/
theorem Number.operator_div_overflow_downward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      x.toRat / y.toRat < -Number.top ∧
      ∃ result,
        x.operator_div y .downward = .ok result := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.div_topGap_low_neg
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonpos (show x.toRat / y.toRat ≤ 0 by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, hhi,
    (Number.operator_div_ok_iff_proof x y _ hx hy hx0 hy0).mpr
      (by show _ < Number.top_plus_one; rw [habs]; linarith)⟩

/-- `upward` `x / y` fails with an overflow error when the exact quotient is at most `-Number.top_plus_ten` or above
`Number.top`. `hrange` leaves out the quotients where the early overflow check differs (FV_M1_19). -/
theorem Number.operator_div_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hrange : x.toRat / y.toRat ≤ Number.top ∨ Number.top_plus_one ≤ x.toRat / y.toRat)
    (h : x.toRat / y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat / y.toRat) :
    ∃ err, x.operator_div y .upward = .error err ∧ isOverflow err = true :=
  Number.operator_div_overflow_proof x y .upward hx hy hx0 hy0
    (topGap_overflow_upward_iff.mpr hrange h)

/-- A quotient left out by `hrange`: it is above `Number.top`, and `upward` `x / y` returns a result. -/
theorem Number.operator_div_overflow_upward_attained :
    ∃ x y : Number,
      x.isNormalized ∧
      y.isNormalized ∧
      x.mantissa_ ≠ 0 ∧
      y.mantissa_ ≠ 0 ∧
      Number.top < x.toRat / y.toRat ∧
      ∃ result,
        x.operator_div y .upward = .ok result := by
  obtain ⟨x, y, hx, hy, hx0, hy0, hlo, hhi⟩ := Number.div_topGap_low_pos
  obtain ⟨hL, hLR, hRM, hMN⟩ := Number.topGap_order
  have habs := abs_of_nonneg (show 0 ≤ x.toRat / y.toRat by linarith)
  exact ⟨x, y, hx, hy, hx0, hy0, hlo,
    (Number.operator_div_ok_iff_proof x y _ hx hy hx0 hy0).mpr
      (by show _ < Number.top_plus_one; rw [habs]; linarith)⟩

/-- In `to_nearest`, `x * y` fails with an overflow error when the exact product is at least `Number.top_plus_five` in
size. -/
theorem Number.operator_mul_overflow_to_nearest (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_five ≤ |x.toRat * y.toRat|) :
    ∃ err, x.operator_mul y .to_nearest = .error err ∧ isOverflow err = true :=
  Number.operator_mul_overflow_to_nearest_proof x y hx hy hx0 hy0 h

/-- In `towards_zero`, `x * y` fails with an overflow error when the exact product is at least `Number.top_plus_ten` in
size. -/
theorem Number.operator_mul_overflow_towards_zero (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : Number.top_plus_ten ≤ |x.toRat * y.toRat|) :
    ∃ err, x.operator_mul y .towards_zero = .error err ∧ isOverflow err = true :=
  Number.operator_mul_overflow_towards_zero_proof x y hx hy hx0 hy0 h

/-- In `downward`, `x * y` fails with an overflow error when the exact product is below `-Number.top` or at least
`Number.top_plus_ten`. -/
theorem Number.operator_mul_overflow_downward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : x.toRat * y.toRat < -Number.top ∨ Number.top_plus_ten ≤ x.toRat * y.toRat) :
    ∃ err, x.operator_mul y .downward = .error err ∧ isOverflow err = true :=
  Number.operator_mul_overflow_downward_proof x y hx hy hx0 hy0 h

/-- In `upward`, `x * y` fails with an overflow error when the exact product is at most `-Number.top_plus_ten` or above
`Number.top`. -/
theorem Number.operator_mul_overflow_upward (x y : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (h : x.toRat * y.toRat ≤ -Number.top_plus_ten ∨ Number.top < x.toRat * y.toRat) :
    ∃ err, x.operator_mul y .upward = .error err ∧ isOverflow err = true :=
  Number.operator_mul_overflow_upward_proof x y hx hy hx0 hy0 h

end XRPL.Model.Protocol
