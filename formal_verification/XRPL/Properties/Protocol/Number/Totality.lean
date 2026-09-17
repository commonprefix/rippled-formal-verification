import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Rounding.BitVec
import XRPL.Properties.Protocol.Number.Common.Rounding.DivQuotient
import XRPL.Properties.Protocol.Number.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Div.RoundsWithin
import XRPL.Properties.Protocol.Number.Sub.RoundsWithin
import XRPL.Properties.Protocol.Number.ToRep.ToRep
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral

/-! # Forward totality of the `Number` pipeline

Success conditions for `doRoundUp`, `doNormalize`, `doNormalize128`, `operator_mul`, `operator_div`
and `operator_sub` on normalized operands with exponent headroom. Split out of the vault withdraw
totality file so that Number-level consumers (the lending invariants) need not import vault proofs. -/

namespace XRPL.Model.Protocol

/-- `operator_neg` of a mantissa-zero `Number` is the canonical zero. -/
theorem Number.operator_neg_of_mantissa_zero (n : Number) (h : n.mantissa_ = 0) :
    n.operator_neg = Number.zero := by
  unfold Number.operator_neg
  rw [if_pos (by rw [h]; rfl)]

/-- Adding the canonical zero on the right is the identity, and total. -/
theorem Number.operator_add_zero_right (x : Number) (mode : rounding_mode) :
    x.operator_add Number.zero mode = .ok x := by
  unfold Number.operator_add
  rw [if_pos (by decide : Number.zero.operator_eq Number.zero = true)]
  rfl

/-- Subtracting a mantissa-zero `Number` is the identity, and total. This is how
a reachable vault's zero loss drops out of the pricing prefix. -/
theorem Number.operator_sub_of_mantissa_zero (x y : Number) (mode : rounding_mode)
    (h : y.mantissa_ = 0) :
    x.operator_sub y mode = .ok x := by
  unfold Number.operator_sub
  rw [Number.operator_neg_of_mantissa_zero y h, Number.operator_add_zero_right]

/-! ## Escaping the zero guards of `operator_mul` / `operator_div`

`operator_div` opens with a divide-by-zero guard keyed on `operator_eq Number.zero`;
a nonzero divisor (here `0 < sharesTotal`, so `mantissa_ ≠ 0`) escapes it, reducing
the divide totality to `doNormalize128`. -/

/-- `operator_eq Number.zero` detects a zero mantissa, so a nonzero mantissa is not
equal to the canonical zero. -/
theorem Number.operator_eq_zero_false_of_mantissa_ne (n : Number) (h : n.mantissa_ ≠ 0) :
    n.operator_eq Number.zero = false := by
  unfold Number.operator_eq
  have : (n.mantissa_ == Number.zero.mantissa_) = false := by
    simp only [Number.zero]; exact beq_false_of_ne h
  simp [this]

/-- **Divide-by-zero escape.** With a nonzero divisor the divide reduces to the
`doNormalize128` pipeline (past the divide-by-zero guard), isolating the divide
totality to that stage. -/
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

/-! ## Forward totality of `Guard.doRoundUp`

`doRoundUp` is the shared tail of `operator_mul` and `operator_add` (hence
`operator_sub`). Its only error is the final overflow check `res.exponent_ >
maxExponent`, and the rounding result never raises the exponent above the input
`e + 1` (`bringIntoRange` keeps or lowers it, only the carry drop-digit leg bumps
it by one). So a source exponent bounded by `maxExponent - 1` guarantees success. -/

/-- **Forward totality of `doRoundUp`.** When the source exponent is at most
`maxExponent - 1`, the rounding step cannot overflow, so it returns `.ok`. -/
theorem Guard.doRoundUp_ok_of_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error)
    (he : e + 1 ≤ maxExponent) :
    ∃ res, g.doRoundUp neg m e minM maxM mode loc = .ok res := by
  unfold Guard.doRoundUp Guard.bringIntoRange
  simp only [Guard.doDropDigit]
  unfold maxExponent minExponent at *
  split_ifs <;>
    first
      | exact ⟨_, rfl⟩
      | (exfalso; simp only [] at *; omega)

/-- **`doRoundUp` output exponent bound.** The rounding step never raises the
exponent above the source `e + 1`: `bringIntoRange` keeps or lowers it, and only
the carry drop-digit leg bumps it once. (The flush sentinel is far below any
`e ≥ minExponent`.) This bounds the tail of `operator_mul` and `operator_add`. -/
theorem Guard.doRoundUp_ok_output_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (he_lo : minExponent ≤ e)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res) :
    res.exponent_ ≤ e + 1 := by
  unfold Guard.doRoundUp Guard.bringIntoRange at hok
  simp only [Guard.doDropDigit] at hok
  unfold maxExponent minExponent at *
  split_ifs at hok <;>
    injection hok with hok' <;>
    subst hok' <;>
    simp only [] <;>
    omega

/-! ## Forward totality of the `doNormalize` back half

`doNormalize`'s only error sites past `scaleUp` are `scaleDown` (mantissa above
`maxMantissa` at `maxExponent`), `capAtMaxRep` (mantissa above `maxRepUp` at
`maxExponent`), and the final `doRoundUp`. For an operand already inside the
mantissa range with a bounded exponent, `scaleDown` is the identity, `capAtMaxRep`
does at most one safe digit drop, and `doRoundUp` succeeds by the linchpin above.
This is exactly the final `res.toNumber.normalize` stage of `operator_mul` and the
same-sign leg of `operator_add`. -/

/-- **Forward totality of `capAtMaxRep`.** Below `maxExponent` it never errors: it
either keeps the mantissa or drops one digit (raising the exponent by one). -/
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

/-- **Forward totality of `doNormalize` for an in-range operand.** A nonzero
mantissa already in `[minM, maxM]` with exponent bounded by `maxExponent - 2`
normalizes without error. -/
theorem doNormalize_ok_of_inRange (neg : Bool) (M : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode)
    (hM0 : M ≠ 0) (hlo : minM ≤ M) (hhi : M ≤ maxM)
    (he_lo : minExponent ≤ e) (he_hi : e + 2 ≤ maxExponent) :
    ∃ res, doNormalize neg M e minM maxM mode = .ok res := by
  unfold doNormalize
  rw [if_neg (show ¬ (M == 0) = true from by simp [hM0])]
  simp only [doNormalize_scaleUp_id minM M e hlo]
  rw [doNormalize_scaleDown_id maxM M e _ hhi]
  simp only []
  rw [if_neg (show ¬ (decide (e < minExponent) || decide (M < minM)) = true from by
    have h1 : decide (e < minExponent) = false := decide_eq_false (by omega)
    have h2 : decide (M < minM) = false :=
      decide_eq_false (by
        rw [UInt64.lt_iff_toNat_lt]
        exact Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp hlo))
    rw [h1, h2]; simp)]
  obtain ⟨m', e', g', hcap, hle⟩ :=
    doNormalize_capAtMaxRep_ok_of_exp M e
      (if neg then Guard.new.set_negative else Guard.new) (by omega)
  rw [hcap]
  simp only []
  obtain ⟨res, hres⟩ :=
    Guard.doRoundUp_ok_of_exp_le g' neg m' e' minM maxM mode .normalize2 (by omega)
  rw [hres]
  exact ⟨res.toNumber, rfl⟩

/-! ## Forward output bound for the `scaleDown128` front-half loop

`scaleDown128` is the shared front-half loop of `operator_mul`'s normalize and
`operator_div`'s `doNormalize128`: it divides a `UInt128` mantissa by ten and
raises the exponent by one until the mantissa drops to `maxRepUp`. Emptying a
vault needs its output exponent bounded so the tail `Guard.doRoundUp_ok_of_exp_le`
fires: the output exponent stays within `e + 20`, because a `UInt128 < 2 ^ 128`
needs at most twenty digit drops to reach `maxRepUp` (`≈ 2 ^ 63`). -/

/-- **`scaleDown128` iteration-count invariant.** The loop runs `k` steps, so the
output exponent is exactly `e + k` and the output mantissa meets the exit bound
`≤ maxRepUp`. Every step past the first forces another power of ten into the input
mantissa above `maxRepUp + 1 = 9223372036854775811`, which caps `k` once the input
is known to fit in `2 ^ 128`. -/
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

/-- **`scaleDown128` output bound.** The digit-drop loop stops once the mantissa
reaches `maxRepUp`, and a `UInt128 < 2 ^ 128` input needs at most twenty drops, so
the output exponent stays within `[e, e + 20]` and the output mantissa within the
exit bound `≤ maxRepUp`. The exponent bracket feeds `Guard.doRoundUp_ok_of_exp_le`:
a source exponent `≤ maxExponent - 21` keeps the multiply / divide tail total. -/
theorem scaleDown128_output_bound (M : UInt128) (e : Int) (g0 : Guard) :
    (scaleDown128 M e g0).1.toNat ≤ maxRepUp.toNat ∧
    e ≤ (scaleDown128 M e g0).2.1 ∧
    (scaleDown128 M e g0).2.1 ≤ e + 20 := by
  obtain ⟨k, hek, hm, hinv⟩ := scaleDown128_forward_exp_bound M e g0
  have hk20 : k ≤ 20 := by
    by_contra hgt
    push_neg at hgt
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

/-! ## Forward totality of `operator_mul` on two normalized operands

`operator_mul` is the first fully-total operator of the withdraw pricing chain.
This composes the pieces above into a `.ok` for the multiply used by the emptying
run (`navN * 1`, where both operands carry a mantissa in `largeRange`, so their
`UInt128` product exceeds `maxRepUp` and the front-half loop always runs).

The proof escapes the two zero guards, keeps the well-founded `scaleDown128` and
`doNormalize` recursions opaque, and bounds the pipeline exponent so both the mid
`doRoundUp` and the final `normalize` succeed:

* the `UInt128` product is `x.mantissa_ * y.mantissa_`, so with both mantissas at
  least `10 ^ 18` it exceeds `maxRepUp`. `scaleDown128_lower_bound` then puts the
  loop output mantissa at or above `mantissaFloor`, and `scaleDown128_output_bound`
  keeps it at or below `maxRepUp` with the exponent inside `[ze, ze + 20]`.
* the mid `doRoundUp` is `.ok` by `Guard.doRoundUp_ok_of_exp_le` (its output
  exponent is at most `ze + 21`, which the hypothesis keeps below `maxExponent`).
* the final `normalize` is total. On a flushed (zero) mantissa it takes the
  `mantissa == 0` branch. Otherwise the `doRoundUp` output invariants
  (`doRoundUp_output_invariants_upTo_maxRepUp_anyMode`) place the mantissa in
  `largeRange`, and `doNormalize_id` returns it unchanged. -/

/-- **Forward totality of `operator_mul` for two `largeRange`-floored operands.**
When both mantissas are at least `largeRange.min` (so nonzero and product above
`maxRepUp`) and the product exponent `x.exponent_ + y.exponent_` sits in
`[minExponent, maxExponent - 22]`, the multiply reaches a success in every mode. -/
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
  -- the final normalize is total: a flushed mantissa takes the zero branch, an
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

/-- **Forward totality of `operator_mul` on two normalized nonzero operands.** The
caller-facing form of `Number.operator_mul_ok_of_large_operands`. This is the
`navN * 1` multiply of the emptying run, where `navN` (the net asset value) and the
share `Number` one are both normalized. The product exponent must sit in
`[minExponent, maxExponent - 22]`, which the emptying caller has from its
`hcap`-derived exponent bound on `navN`. -/
theorem Number.operator_mul_ok_of_normalized
    (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx0 : x.mantissa_ ≠ 0) (hy0 : y.mantissa_ ≠ 0)
    (he_lo : minExponent ≤ x.exponent_ + y.exponent_)
    (he_hi : x.exponent_ + y.exponent_ ≤ maxExponent - 22) :
    ∃ result, x.operator_mul y mode = .ok result :=
  Number.operator_mul_ok_of_large_operands x y mode
    (hx.mantissaBounds hx0).1 (hy.mantissaBounds hy0).1 he_lo he_hi

/-! ## Forward totality of `operator_div` on two normalized operands

`operator_div` is the next operator of the withdraw pricing chain
(`NAVShares / sharesTotal`). It mirrors the multiply composition: escape the
divide-by-zero guard, keep the well-founded recursions opaque, and bound the
pipeline exponent so the whole back half succeeds.

The front half is the straight-line `divQuotient128` (a 128-bit staged divide,
no loop) whose quotient exponent is `x.exponent_ - y.exponent_ - N` with
`N ∈ {17, 22}` (`divQuotient128_correct`), so it never exceeds
`x.exponent_ - y.exponent_ - 17`. The back half `doNormalize128` differs from
`doNormalize` only in operating on a `UInt128`: an inner `scaleUp` (which only
lowers the exponent), then `doNormalize_scaleDown128` (a divide-by-ten loop that
errors only if the exponent reaches `maxExponent` before the mantissa drops to
`maxMantissa`), then the shared `capAtMaxRep` / `doRoundUp` tail.

Totality of the back half needs only an *exponent* bound: the input mantissa is a
`UInt128`, hence `< 2 ^ 128 < 10 ^ 39 = (maxMantissa + 1) · 10 ^ 20`, so at most
twenty drops reach `maxMantissa`, keeping the output exponent within `e + 20`; the
tail then adds at most two. So `e + 22 ≤ maxExponent` suffices for `doNormalize128`,
and with the `-17` divide offset the caller needs
`x.exponent_ - y.exponent_ ≤ maxExponent - 5`. -/

/-- **`doNormalize128.scaleUp` lowers the exponent.** The scale-up loop only
multiplies the mantissa and decrements the exponent, so its output exponent never
exceeds the input. -/
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

/-- **Forward totality of `doNormalize_scaleDown128`.** A `UInt128` mantissa within
`(maxMantissa + 1) · 10 ^ d` needs at most `d` divide-by-ten drops to reach
`maxMantissa`, and the loop errors only when it must drop while the exponent has
already hit `maxExponent`. So a source exponent with `d` steps of headroom
(`e + d ≤ maxExponent`) keeps the loop total, and the output exponent stays within
`e + d`. Proved by induction on the headroom `d`, whose value is the loop invariant:
each fired drop lowers the mantissa magnitude by one power of ten while raising the
exponent by one, so `e + d` is preserved. -/
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

/-- **Forward totality of `doNormalize128`.** With the source exponent bounded by
`maxExponent - 22`, every stage of the `UInt128` normalize pipeline succeeds. The
magnitude budget is free: the input mantissa is a `UInt128`, so `< 2 ^ 128 < 10 ^ 39`,
and twenty drops suffice. The exponent budget carries: `scaleUp` only lowers it, the
scale-down adds at most twenty, `capAtMaxRep` at most one, and `doRoundUp` at most one
more. No mantissa bound and no lower exponent bound are needed (a zero or underflowing
mantissa takes the canonical-zero exit). -/
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

/-- **Forward totality of `operator_div` on two normalized nonzero operands.** This
is the `NAVShares / sharesTotal` divide of the emptying run, where the dividend
(net-asset-value share) and divisor (`sharesTotal`, nonzero from `0 < sharesTotal`)
are both normalized. The quotient exponent `x.exponent_ - y.exponent_` must sit at
or below `maxExponent - 5`, which (with the `divQuotient128` `-17` scale offset)
gives the `doNormalize128` stage the `e + 22 ≤ maxExponent` headroom it needs. -/
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

/-! ## Forward totality of `operator_sub` on two normalized capped operands

`operator_sub x y` is `operator_add x y.operator_neg`. The withdraw run performs
two such subtractions, each decrementing a nonnegative stored total by a
nonnegative normalized `Number` that fits `2 ^ 63 - 1`: the assets total minus the
priced payout, and the share total minus the burned shares. Negating a nonnegative
`y` flips its sign, so the internal addition always takes the different-sign
branch, which routes through the `recover` loop and `doNormalize128`. Totality of
that branch needs only an exponent bound. A normalized nonnegative `Number` capped
by `2 ^ 63 - 1` has a nonpositive raw exponent (`Number.exponent_fn_le_zero_of_cap`
lifted through `Number.exponent_ ≤ Number.exponent`). The aligned common exponent
is the maximum of the two (`alignDown_e_eq`), and the `recover` loop only lowers it
(`recover_exponent_le`). So the `doNormalize128` input exponent stays at or below
zero, well inside the `maxExponent - 22` headroom of `doNormalize128_ok_of_exp`. No
ordering of the operands is required, and the result magnitude is irrelevant to
totality. -/

/-- **Forward totality of the different-sign `operator_add` tail.** The `recover`
loop followed by `doNormalize128` is total whenever the pre-`recover` exponent is
nonpositive. This is agnostic to the result sign, the pre-`recover` mantissa and
the guard, because `recover` only decreases the exponent (`recover_exponent_le`)
and the tail keeps 22 steps of headroom to `maxExponent`. -/
private lemma Number.diffSign_recover_tail_ok (zn : Bool) (m : UInt128) (E : Int)
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

/-- **Forward totality of the different-sign `operator_add`.** A nonzero second
operand of opposite sign to the first, with both raw exponents nonpositive, reaches
a success. The zero and exact-cancellation guards short-circuit to a success, and
the different-sign body reduces to `Number.diffSign_recover_tail_ok`. The aligned
common exponent is `max x.exponent_ y.exponent_ ≤ 0` (`alignDown_e_eq`), which
feeds the tail. -/
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

/-- **Forward totality of `operator_sub` for two normalized nonnegative operands with exponent
headroom.** The same shape as the capped version below, with the exponent bound `doNormalize128`
needs given directly: 22 steps below `maxExponent`. A zero subtrahend is the identity, otherwise
the negated subtrahend has the opposite sign to `x` and the different-sign add is total. -/
theorem Number.operator_sub_ok_of_normalized_exp (x y : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxneg : x.negative_ = false) (hyneg : y.negative_ = false)
    (hxe : x.exponent_ + 22 ≤ maxExponent) (hye : y.exponent_ + 22 ≤ maxExponent) :
    ∃ result, x.operator_sub y mode = .ok result := by
  by_cases hy0 : y.mantissa_ = 0
  · exact ⟨x, Number.operator_sub_of_mantissa_zero x y mode hy0⟩
  · have hkey : y.operator_neg = { y with negative_ := !y.negative_ } := by
      unfold Number.operator_neg
      rw [if_neg (ne_true_of_eq_false (beq_false_of_ne hy0))]
    unfold Number.operator_sub
    apply Number.operator_add_diffSign_ok x y.operator_neg mode
    · rw [hkey]; exact hy0
    · rw [hkey]; simp only [hxneg, hyneg]; rfl
    · exact hxe
    · rw [hkey]; exact hye


end XRPL.Model.Protocol
