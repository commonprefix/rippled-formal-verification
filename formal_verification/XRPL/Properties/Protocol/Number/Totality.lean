import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.Number.Common.Rounding.DivQuotient
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Compare.Compare

/-! # When the `Number` operations succeed

Success conditions for `doRoundUp`, `doNormalize`, `doNormalize128`, `operator_mul`, `operator_div`
and `operator_sub` on normalized operands with exponent headroom. -/

namespace XRPL.Model.Protocol

/-- `operator_neg` of a mantissa-zero `Number` is the canonical zero. -/
theorem Number.operator_neg_of_mantissa_zero (n : Number) (h : n.mantissa_ = 0) :
    n.operator_neg = Number.zero := by
  unfold Number.operator_neg
  rw [if_pos (by rw [h]; rfl)]

/-- Adding the canonical zero on the right is the identity and never errors. -/
theorem Number.operator_add_zero_right (x : Number) (mode : rounding_mode) :
    x.operator_add Number.zero mode = .ok x := by
  unfold Number.operator_add
  rw [if_pos (by decide : Number.zero.operator_eq Number.zero = true)]
  rfl

/-- Adding the canonical zero on the left returns the other operand and never errors. -/
theorem Number.operator_add_zero_left (y : Number) (mode : rounding_mode) :
    Number.zero.operator_add y mode = .ok y := by
  unfold Number.operator_add
  by_cases hy : y.operator_eq Number.zero = true
  · rw [if_pos hy, (Number.operator_eq_iff_eq y Number.zero).mp hy]; rfl
  · rw [if_neg hy, if_pos (by decide : Number.zero.operator_eq Number.zero = true)]; rfl

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
       else
         let zn := x.negative_ != y.negative_
         let (zm128, ze, dropped) :=
           divQuotient128 x.mantissa_ y.mantissa_ x.exponent_ y.exponent_
         doNormalize128 zn zm128 ze largeRange.min largeRange.max mode dropped) := by
  unfold Number.operator_div
  rw [Number.operator_eq_zero_false_of_mantissa_ne y hy, if_neg Bool.false_ne_true]

/-- `doRoundUp` succeeds when the source exponent is at most `maxExponent - 1`, since the rounding step cannot
overflow. -/
theorem Guard.doRoundUp_ok_of_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error)
    (he : e + 1 ≤ maxExponent) :
    ∃ res, g.doRoundUp neg m e minM maxM mode loc = .ok res := by
  unfold Guard.doRoundUp Guard.bringIntoRange
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
  unfold Guard.doRoundUp Guard.bringIntoRange at hok
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
  · rw [if_pos h, if_neg (show ¬ e ≥ maxExponent from not_le.mpr he)]
    exact ⟨(divu10 m).1, e + 1, g.push (divu10 m).2, rfl, le_refl _⟩
  · rw [if_neg h]
    exact ⟨m, e, g, rfl, by omega⟩

/-- `scaleDown128` runs some `k` steps: the output exponent is `e + k`, the output mantissa is `≤ maxRepUp`, and
`k ≥ 1` forces the input mantissa to be at least `9223372036854775811 * 10^(k - 1)`. -/
theorem scaleDown128_forward_exp_bound (M : UInt128) (e : Int) (g0 : Guard) :
    ∃ k : ℕ,
      (scaleDown128 M e g0).2.1 = e + (k : Int) ∧
      (scaleDown128 M e g0).1.toNat ≤ maxRepUp.toNat ∧
      (1 ≤ k → 9223372036854775811 * 10 ^ (k - 1) ≤ M.toNat) := by
  induction M, e, g0 using scaleDown128.induct with
  | case1 M e g0 hcond d IH =>
    have hd_def : d = toUInt64 (M % 10) := rfl
    have h10_128 : (10 : UInt128).toNat = 10 := by decide
    have hM10_nat : (M / 10 : UInt128).toNat = M.toNat / 10 := by
      rw [BitVec.toNat_udiv, h10_128]
    have hM_gt : M.toNat > maxRepUp.toNat := by
      have := BitVec.lt_def.mp hcond
      rwa [toNat_toUInt128] at this
    have hunfold : scaleDown128 M e g0
        = scaleDown128 (M / 10) (e + 1) (g0.push d) := by
      conv_lhs => rw [scaleDown128]
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
    have hexit : scaleDown128 M e g0 = (toUInt64 M, e, g0) := by
      unfold scaleDown128
      simp [hcond]
    rw [hexit]
    refine ⟨0, by simp, ?_, ?_⟩
    · show (toUInt64 M).toNat ≤ maxRepUp.toNat
      rw [toNat_toUInt64 hfit]; exact hM_le
    · intro h; exact absurd h (by omega)

/-- `scaleDown128` returns a mantissa `≤ maxRepUp` and an exponent in `[e, e + 20]`, since a `UInt128` input
needs at most twenty digit drops. -/
theorem scaleDown128_output_bound (M : UInt128) (e : Int) (g0 : Guard) :
    (scaleDown128 M e g0).1.toNat ≤ maxRepUp.toNat ∧
    e ≤ (scaleDown128 M e g0).2.1 ∧
    (scaleDown128 M e g0).2.1 ≤ e + 20 := by
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
  unfold Number.operator_mul
  rw [Number.operator_eq_zero_false_of_mantissa_ne x hx]
  rw [Number.operator_eq_zero_false_of_mantissa_ne y hy]
  simp only [Bool.false_eq_true, if_false]
  set zn := x.negative_ != y.negative_ with hzn_def
  set M := toUInt128 x.mantissa_ * toUInt128 y.mantissa_ with hM_def
  set ze := x.exponent_ + y.exponent_ with hze_def
  set g0 := if zn = true then Guard.new.set_negative else Guard.new with hg0_def
  set sd := scaleDown128 M ze g0 with hsd_def
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
    largeRange.min largeRange.max mode .overflow (by omega)
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
    unfold doNormalize
    rw [if_pos (show (res.toNumber.mantissa_ == 0) = true from by
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
theorem Number.operator_mul_ok_of_normalized
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (he_lo : minExponent ≤ x.exponent_ + y.exponent_)
    (he_hi : x.exponent_ + y.exponent_ ≤ maxExponent - 22) :
    ∃ result, x.operator_mul y mode = .ok result :=
  Number.operator_mul_ok_of_large_operands x y mode
    (hx.mantissaBounds hx0).1 (hy.mantissaBounds hy0).1 he_lo he_hi

/-- `doNormalize128.scaleUp` never raises the exponent, since it only multiplies the mantissa by 10 and
decrements the exponent. -/
theorem doNormalize128_scaleUp_exp_le (minMant : UInt64) (m : UInt128) (e : Int) :
    (doNormalize128.scaleUp minMant m e).2 ≤ e := by
  induction m, e using doNormalize128.scaleUp.induct (minMantissa := minMant) with
  | case1 m e hcond IH =>
    rw [show doNormalize128.scaleUp minMant m e
        = doNormalize128.scaleUp minMant (m * 10) (e - 1) from by
      rw [doNormalize128.scaleUp.eq_def]
      simp only [if_pos hcond]]
    omega
  | case2 m e hcond =>
    have h : doNormalize128.scaleUp minMant m e = (m, e) := by
      rw [doNormalize128.scaleUp.eq_def]; simp only [if_neg hcond]
    rw [h]

/-- If the mantissa is below `(maxMantissa + 1) · 10^d` and `e + d ≤ maxExponent`, `doNormalize_scaleDown128`
succeeds with an output exponent at most `e + d`. -/
theorem doNormalize_scaleDown128_ok_aux (d : ℕ) :
    ∀ (m : UInt128) (e : Int) (g : Guard),
      m.toNat < (largeRange.max.toNat + 1) * 10 ^ d →
      e + (d : Int) ≤ maxExponent →
      ∃ (m' : UInt128) (e' : Int) (g' : Guard),
        doNormalize_scaleDown128 largeRange.max m e g = .ok (m', e', g') ∧
        e' ≤ e + (d : Int) := by
  induction d with
  | zero =>
    intro m e g hm _he
    have hmle : m.toNat ≤ largeRange.max.toNat := by
      rw [pow_zero, mul_one] at hm; omega
    have hnotgt : ¬ m > toUInt128 largeRange.max := by
      rw [gt_iff_lt, BitVec.lt_def, toNat_toUInt128]; omega
    refine ⟨m, e, g, ?_, ?_⟩
    · rw [doNormalize_scaleDown128.eq_def, dif_neg hnotgt]
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
      · rw [doNormalize_scaleDown128.eq_def, dif_pos hgt, if_neg hne]; exact hok
      · push_cast at hle ⊢; omega
    · refine ⟨m, e, g, ?_, ?_⟩
      · rw [doNormalize_scaleDown128.eq_def, dif_neg hgt]
      · push_cast; omega

/-- `doNormalize128` succeeds whenever the source exponent is at most `maxExponent - 22`, with no mantissa
bound and no lower exponent bound. -/
theorem doNormalize128_ok_of_exp (zn : Bool) (M : UInt128) (e : Int)
    (mode : rounding_mode) (sticky : Bool) (he : e + 22 ≤ maxExponent) :
    ∃ result, doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result := by
  by_cases hM0 : (M == 0) = true
  · exact ⟨Number.zero, by unfold doNormalize128; rw [if_pos hM0]⟩
  · unfold doNormalize128
    rw [if_neg hM0]
    simp only []
    rcases hsu : doNormalize128.scaleUp largeRange.min M e with ⟨M₁, e₁⟩
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
    · rw [if_pos hund]; exact ⟨Number.zero, rfl⟩
    · rw [if_neg hund]
      obtain ⟨m'', e'', g'', hcap, hle''⟩ :=
        doNormalize_capAtMaxRep_ok_of_exp (toUInt64 m') e' g' (by push_cast at hle'; omega)
      rw [hcap]
      simp only []
      obtain ⟨res, hru⟩ :=
        Guard.doRoundUp_ok_of_exp_le g'' zn m'' e'' largeRange.min largeRange.max mode
          .normalize2 (by push_cast at hle' hle''; omega)
      rw [hru]
      exact ⟨res.toNumber, rfl⟩

/-- `operator_div` succeeds in every mode on two normalized nonzero operands with
`x.exponent_ - y.exponent_ ≤ maxExponent - 5`, which leaves `doNormalize128` the headroom it needs. -/
theorem Number.operator_div_ok_of_normalized
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (he : x.exponent_ - y.exponent_ ≤ maxExponent - 5) :
    ∃ result, x.operator_div y mode = .ok result := by
  have hxb := hx.mantissaBounds hx0
  have hyb := hy.mantissaBounds hy0
  obtain ⟨zmq, zeq, drp, N, r, hdq, htail⟩ :=
    divQuotient128_correct x.mantissa_ y.mantissa_ x.exponent_ y.exponent_
      (mantissa_toNat_pos_of_bounds hxb)
      (mantissa_toNat_pos_of_bounds hyb)
      (UInt64.le_iff_toNat_le.mp hxb.2)
      (UInt64.le_iff_toNat_le.mp hyb.2)
      (UInt64.le_iff_toNat_le.mp hyb.1)
  obtain ⟨hN, -, -, hzeq, -, -⟩ := htail
  have hze : zeq + 22 ≤ maxExponent := by rcases hN with rfl | rfl <;> omega
  have hxeq : x.operator_eq Number.zero = false :=
    Number.operator_eq_zero_false_of_mantissa_ne x hx0
  rw [Number.operator_div_of_divisor_ne x y mode hy0, hxeq, if_neg Bool.false_ne_true, hdq]
  exact doNormalize128_ok_of_exp (x.negative_ != y.negative_) zmq zeq mode drp hze

/-- The diff-sign `operator_add` tail (`recover` then `doNormalize128`) succeeds for any sign, mantissa and
guard when the pre-`recover` exponent `E` has `E + 22 ≤ maxExponent`, since `recover` never raises it. -/
lemma Number.diffSign_recover_tail_ok (zn : Bool) (m : UInt128) (E : Int)
    (g : Guard) (mode : rounding_mode) (hE : E + 22 ≤ maxExponent) :
    ∃ result, doNormalize128 zn
      (if (Number.operator_add.recover (toUInt128 largeRange.min * 1000) m E g 40).2.2.empty = true
        then (Number.operator_add.recover (toUInt128 largeRange.min * 1000) m E g 40).1
        else (Number.operator_add.recover (toUInt128 largeRange.min * 1000) m E g 40).1 - 1)
      (Number.operator_add.recover (toUInt128 largeRange.min * 1000) m E g 40).2.1
      largeRange.min largeRange.max mode
      (!(Number.operator_add.recover (toUInt128 largeRange.min * 1000) m E g 40).2.2.empty)
    = .ok result := by
  set R := Number.operator_add.recover (toUInt128 largeRange.min * 1000) m E g 40 with hR
  have hle : R.2.1 ≤ E := by rw [hR]; exact recover_exponent_le _ _ _ _ _
  exact doNormalize128_ok_of_exp zn _ R.2.1 mode _ (by omega)

/-- Diff-sign `operator_add` with a nonzero second operand succeeds in every mode when both exponents are at
least 22 below `maxExponent`. -/
private theorem Number.operator_add_diffSign_ok (x y : Number) (mode : rounding_mode)
    (hy0 : y.mantissa_ ≠ 0)
    (hsign : (x.negative_ == y.negative_) = false)
    (hxe : x.exponent_ + 22 ≤ maxExponent) (hye : y.exponent_ + 22 ≤ maxExponent) :
    ∃ result, x.operator_add y mode = .ok result := by
  unfold Number.operator_add
  rw [Number.operator_eq_zero_false_of_mantissa_ne y hy0, if_neg Bool.false_ne_true]
  by_cases hg2 : x.operator_eq Number.zero = true
  · rw [if_pos hg2]; exact ⟨y, rfl⟩
  · rw [if_neg hg2]
    by_cases hg3 : x.operator_eq y.operator_neg = true
    · rw [if_pos hg3]; exact ⟨Number.zero, rfl⟩
    · rw [if_neg hg3]
      simp only [hsign, Bool.false_eq_true, if_false]
      apply Number.diffSign_recover_tail_ok
      split_ifs <;> first | (rw [alignDown_e_eq]; omega) | omega

/-- Two aligned mantissas below `10^19` with sum at least `10^18`, at a common exponent in
`[minExponent, maxExponent - 3]`, add, round and normalize without error. -/
lemma Number.sameSign_add_tail_ok (xn : Bool) (xm_a ym_a : UInt64) (e : Int) (g : Guard)
    (mode : rounding_mode) (hxm : xm_a.toNat < 10 ^ 19) (hym : ym_a.toNat < 10 ^ 19)
    (hsum : 10 ^ 18 ≤ xm_a.toNat + ym_a.toNat)
    (he_lo : minExponent ≤ e) (he_hi : e + 3 ≤ maxExponent) :
    ∃ result, (let zm128 : UInt128 := toUInt128 xm_a + toUInt128 ym_a
      let p : UInt64 × Int × Guard :=
        if zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp then
          (toUInt64 (g.doDropDigit128 zm128 e).2.1, (g.doDropDigit128 zm128 e).2.2,
           (g.doDropDigit128 zm128 e).1)
        else (toUInt64 zm128, e, g)
      match p.2.2.doRoundUp xn p.1 p.2.1 largeRange.min largeRange.max mode .overflow with
      | .error err => Except.error err
      | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode) = .ok result := by
  have hxm_tu : (toUInt128 xm_a).toNat = xm_a.toNat := toNat_toUInt128 xm_a
  have hym_tu : (toUInt128 ym_a).toNat = ym_a.toNat := toNat_toUInt128 ym_a
  set zm128 : UInt128 := toUInt128 xm_a + toUInt128 ym_a with hzm128_def
  have hzm128 : zm128.toNat = xm_a.toNat + ym_a.toNat := by
    rw [hzm128_def, BitVec.toNat_add, hxm_tu, hym_tu]
    apply Nat.mod_eq_of_lt
    have : 2 * 10 ^ 19 < 2 ^ 128 := by norm_num
    omega
  have hmru : (toUInt128 maxRepUp).toNat = 9223372036854775810 := by
    rw [toNat_toUInt128]; rfl
  have hlrm : (toUInt128 largeRange.max).toNat = 9999999999999999999 := by
    rw [toNat_toUInt128]; exact largeRange_max_val
  set p : UInt64 × Int × Guard :=
    if zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp then
      (toUInt64 (g.doDropDigit128 zm128 e).2.1, (g.doDropDigit128 zm128 e).2.2,
       (g.doDropDigit128 zm128 e).1)
    else (toUInt64 zm128, e, g) with hp_def
  -- the rounding input: mantissa in `[mantissaFloor, maxRepUp]`, exponent in `[e, e + 1]`
  have hp : mantissaFloor ≤ p.1.toNat ∧ p.1.toNat ≤ maxRepUp.toNat ∧ e ≤ p.2.1 ∧
      p.2.1 ≤ e + 1 := by
    have hmru' : maxRepUp.toNat = 9223372036854775810 := rfl
    by_cases hc : (zm128 > toUInt128 largeRange.max || zm128 > toUInt128 maxRepUp) = true
    · rw [hp_def, if_pos hc]
      have hgt : 9223372036854775810 < zm128.toNat := by
        rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
        rcases hc with h | h
        · have := BitVec.lt_def.mp h; rw [hlrm] at this; omega
        · have := BitVec.lt_def.mp h; rw [hmru] at this; omega
      have h10 : (10 : UInt128).toNat = 10 := by decide
      have hdiv : (zm128 / 10).toNat = zm128.toNat / 10 := by rw [BitVec.toNat_udiv, h10]
      have hfit : (zm128 / 10).toNat < 2 ^ 64 := by
        rw [hdiv, hzm128]
        have : 2 * 10 ^ 18 < 2 ^ 64 := by norm_num
        omega
      simp only [Guard.doDropDigit128]
      rw [toNat_toUInt64 hfit, hdiv, hmru']
      refine ⟨by omega, by omega, by omega, le_refl _⟩
    · rw [hp_def, if_neg hc]
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, not_or] at hc
      have hle : zm128.toNat ≤ 9223372036854775810 := by
        have h' : ¬ (toUInt128 maxRepUp).toNat < zm128.toNat := fun h => hc.2 (BitVec.lt_def.mpr h)
        rw [hmru] at h'
        omega
      have hfit : zm128.toNat < 2 ^ 64 := by omega
      simp only []
      rw [toNat_toUInt64 hfit, hmru']
      refine ⟨by omega, by omega, le_refl _, by omega⟩
  obtain ⟨hlo, hhi, hze_lo, hze_hi⟩ := hp
  obtain ⟨res, hres⟩ := Guard.doRoundUp_ok_of_exp_le p.2.2 xn p.1 p.2.1
    largeRange.min largeRange.max mode .overflow (by omega)
  show ∃ result, (match p.2.2.doRoundUp xn p.1 p.2.1 largeRange.min largeRange.max mode
      .overflow with
    | .error err => Except.error err
    | .ok res => res.toNumber.normalize largeRange.min largeRange.max mode) = .ok result
  rw [hres]
  simp only []
  have hexp_out : res.exponent_ ≤ p.2.1 + 1 :=
    Guard.doRoundUp_ok_output_exp_le p.2.2 xn p.1 p.2.1 largeRange.min largeRange.max mode
      .overflow res (by omega) hres
  by_cases hrm : res.mantissa_ = 0
  · refine ⟨Number.zero, ?_⟩
    show doNormalize res.toNumber.negative_ res.toNumber.mantissa_ res.toNumber.exponent_
      largeRange.min largeRange.max mode = .ok Number.zero
    unfold doNormalize
    rw [if_pos (show (res.toNumber.mantissa_ == 0) = true from by
      show (res.mantissa_ == 0) = true; rw [beq_iff_eq]; exact hrm)]
  · obtain ⟨h_res_min, h_res_max, h_res_exp, h_res_mod⟩ :=
      doRoundUp_output_invariants_upTo_maxRepUp_anyMode p.2.2 xn p.1 p.2.1 mode hlo hhi
        .overflow res hres hrm
    exact ⟨res.toNumber, doNormalize_id mode res.negative_ res.mantissa_ res.exponent_
      h_res_min h_res_max h_res_exp h_res_mod (by omega) (fun _ => by omega)⟩

/-- The `Number` exponent of a nonzero normalized source sits at or above `minExponent`. -/
lemma Number.exponent_ge_min (n : Number) (hn : n.isNormalized) (hn0 : n.mantissa_ ≠ 0) :
    minExponent ≤ n.exponent_ := by
  rcases hn with hz | ⟨_, _, _, hemin, _⟩
  · exfalso; apply hn0; rw [hz]; rfl
  · exact hemin

/-- Same-sign `operator_add` succeeds. Two nonzero normalized operands of the same sign, each exponent at least
3 below `maxExponent`, add without error in every mode. -/
lemma Number.operator_add_sameSign_ok (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (hsign : x.negative_ = y.negative_)
    (hxe : x.exponent_ + 3 ≤ maxExponent) (hye : y.exponent_ + 3 ≤ maxExponent) :
    ∃ result, x.operator_add y mode = .ok result := by
  have hxe_min := Number.exponent_ge_min x hx hx0
  have hye_min := Number.exponent_ge_min y hy hy0
  have hx_b := mantissaBounds_nat_of (hx.mantissaBounds hx0)
  have hy_b := mantissaBounds_nat_of (hy.mantissaBounds hy0)
  unfold Number.operator_add
  rw [Number.operator_eq_zero_false_of_mantissa_ne y hy0,
    Number.operator_eq_zero_false_of_mantissa_ne x hx0]
  simp only [Bool.false_eq_true, if_false]
  by_cases hc : x.operator_eq y.operator_neg = true
  · rw [if_pos hc]; exact ⟨Number.zero, rfl⟩
  rw [if_neg hc]
  have hsn : (x.negative_ == y.negative_) = true := by rw [beq_iff_eq]; exact hsign
  by_cases hlt : x.exponent_ < y.exponent_
  · rw [if_pos hlt]
    set g₀ : Guard := if x.negative_ then Guard.new.set_negative else Guard.new
    have he := alignDown_e_eq x.mantissa_ x.exponent_ g₀ y.exponent_
    have hm := alignDown_mantissa_le x.mantissa_ x.exponent_ g₀ y.exponent_
    rw [max_eq_right (le_of_lt hlt)] at he
    obtain ⟨r, hr⟩ := Number.sameSign_add_tail_ok x.negative_
      (Number.operator_add.alignDown x.mantissa_ x.exponent_ g₀ y.exponent_).1 y.mantissa_
      (Number.operator_add.alignDown x.mantissa_ x.exponent_ g₀ y.exponent_).2.1
      (Number.operator_add.alignDown x.mantissa_ x.exponent_ g₀ y.exponent_).2.2 mode
      (by omega) hy_b.2 (by omega) (by rw [he]; exact hye_min) (by rw [he]; exact hye)
    exact ⟨r, by simpa only [hsn, if_true] using hr⟩
  by_cases hgt : x.exponent_ > y.exponent_
  · rw [if_neg hlt, if_pos hgt]
    set g₀ : Guard := if y.negative_ then Guard.new.set_negative else Guard.new
    have he := alignDown_e_eq y.mantissa_ y.exponent_ g₀ x.exponent_
    have hm := alignDown_mantissa_le y.mantissa_ y.exponent_ g₀ x.exponent_
    rw [max_eq_right (le_of_lt hgt)] at he
    obtain ⟨r, hr⟩ := Number.sameSign_add_tail_ok x.negative_ x.mantissa_
      (Number.operator_add.alignDown y.mantissa_ y.exponent_ g₀ x.exponent_).1 x.exponent_
      (Number.operator_add.alignDown y.mantissa_ y.exponent_ g₀ x.exponent_).2.2 mode
      hx_b.2 (by omega) (by omega) hxe_min hxe
    exact ⟨r, by simpa only [hsn, if_true] using hr⟩
  · rw [if_neg hlt, if_neg hgt]
    obtain ⟨r, hr⟩ := Number.sameSign_add_tail_ok x.negative_ x.mantissa_ y.mantissa_ x.exponent_
      (if x.negative_ then Guard.new.set_negative else Guard.new) mode
      hx_b.2 hy_b.2 (by omega) hxe_min hxe
    exact ⟨r, by simpa only [hsn, if_true] using hr⟩

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
    rw [Number.operator_eq_zero_false_of_mantissa_ne y hy0, if_neg Bool.false_ne_true,
      if_pos (by decide)]
    exact ⟨y, rfl⟩
  by_cases hs : x.negative_ = y.negative_
  · exact Number.operator_add_sameSign_ok x y mode hx hy hx0 hy0 hs (by omega) (by omega)
  · exact Number.operator_add_diffSign_ok x y mode hy0 (beq_eq_false_iff_ne.mpr hs) hxe hye

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

end XRPL.Model.Protocol
