import XRPL.Properties.Protocol.Number.Common.Notation
import Mathlib.Tactic

import XRPL.Properties.Protocol.Number.Common.Rounding.ScaleDown

namespace XRPL.Model.Protocol


/-! # `divQuotient128` correctness (staged form, PR 7389 head)

The staged division quotient `divQuotient128 xm ym xe ye` expands the numerator
by `10^17` (Stage 1), refines a nonzero remainder by a further `10^5`
(Stage 2 — total factor `10^22`), and reports whether any residual survives
(Stage 3, the `dropped` sticky flag).

The key property: `xm · 10^N = zm128 · ym + r` with `0 ≤ r < ym`, `N ∈ {17, 22}`,
`ze = xe - ye - N`, and `dropped = true ↔ r ≠ 0`. This means
`|x/y| = (zm128 + r/ym) · 10^ze` with the sticky flag exactly tracking `r ≠ 0`.
When the Stage-2 correction is zero (`N = 17` with `r ≠ 0` possible), the
residual is tiny: `r · 10^5 < ym`, i.e. `δ = r/ym < 10⁻⁵` — the
`doNormalize128` keystones consume this through their `δ·10^20 ≤ M` ratio
hypothesis.

## Kernel-checkability

The kernel's defeq blows its recursion guard whenever it must relate the full
`divQuotient128` application to a reduced form in one step (`simp`-unfolding,
`extract_lets`, whole-body `change`, and `.1/.2` projection forms all die).
Small steps are fine, so the proof navigates equationally: `unfold` (one
equation), then one single-let zeta `change` per `let` (head-zeta + syntactic
comparison each), then `rw [if_pos/if_neg]` (equations) and per-leaf `rfl`s
whose defeq is one `Prod` iota. -/

abbrev divQuotientTail (zmq : UInt128) (zeq : Int) (dropped : Bool) (N r : ℕ)
    (xm ym : UInt64) (xe ye : Int) : Prop :=
  (N = 17 ∨ N = 22) ∧
  xm.toNat * 10 ^ N = zmq.toNat * ym.toNat + r ∧
  r < ym.toNat ∧
  zeq = xe - ye - N ∧
  (dropped = true ↔ r ≠ 0) ∧
  (N = 17 → r * 10 ^ 5 < ym.toNat)

/-! ### Branch equations

`divQuotient128` is navigated through these three `simp only` equations rather than by
zeta-expanding its body in the main proof: each one resolves the two `if`s from the branch
hypotheses, so the kernel only ever sees a case-resolved body. -/

private lemma divQuotient128_eq_rem_zero (xm ym : UInt64) (xe ye : Int)
    (hrem : ¬ ((toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym) != 0) = true) :
    divQuotient128 xm ym xe ye = (toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym, xe - ye - 17, false) := by
  simp only [divQuotient128, if_neg hrem]

private lemma divQuotient128_eq_corr_ne (xm ym : UInt64) (xe ye : Int)
    (hrem : ((toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym) != 0) = true)
    (hcorr : ((toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128) / toUInt128 ym) != 0) = true) :
    divQuotient128 xm ym xe ye
      = (toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym * (100000 : UInt128)
           + toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128) / toUInt128 ym,
         xe - ye - 17 - 5,
         toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128) % toUInt128 ym != 0) := by
  simp only [divQuotient128, if_pos hrem, if_pos hcorr]

private lemma divQuotient128_eq_corr_zero (xm ym : UInt64) (xe ye : Int)
    (hrem : ((toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym) != 0) = true)
    (hcorr : ¬ ((toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128) / toUInt128 ym) != 0) = true) :
    divQuotient128 xm ym xe ye
      = (toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym, xe - ye - 17,
         toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128) % toUInt128 ym != 0) := by
  simp only [divQuotient128, if_pos hrem, if_neg hcorr]

/-- Branch pins. The `Div/Common/*/WitnessTrace.lean` witnesses cover `correction ≠ 0`;
these cover the other two branches. -/
example : divQuotient128 10 999999999999999989 0 0 = (1, -17, true) := by decide

example : divQuotient128 7 100000000000000000 0 0 = (7, -17, false) := by decide

set_option maxHeartbeats 3200000 in
-- The correction path does UInt128 multiplications by 10^17/10^5; bounding them
-- below 2^128 requires the Euclidean-division chain across two stages. The
-- incremental zeta-expansion blocks add elaboration work on top.
/-- `divQuotient128` satisfies the Euclidean division property:
there exist `N ∈ {17, 22}` and a remainder `r < ym` such that
`xm * 10^N = zm128 * ym + r`, `ze = xe - ye - N`, the `dropped` flag is set
iff `r ≠ 0`, and in the `N = 17` case the residual is tiny (`r·10^5 < ym`).

The output is exposed through an explicit tuple equation; the witnesses are
the spelled-out branch values, and each branch equation closes by a small
`rfl` (one `Prod` iota), keeping every kernel defeq shallow. -/
theorem divQuotient128_correct (xm ym : UInt64) (xe ye : Int)
    (_hxm_pos : 0 < xm.toNat)
    (hym_pos : 0 < ym.toNat)
    (hxm_le : xm.toNat ≤ largeRange.max.toNat)
    (_hym_le : ym.toNat ≤ largeRange.max.toNat)
    (hym_min : largeRange.min.toNat ≤ ym.toNat) :
    ∃ (zmq : UInt128) (zeq : Int) (dropped : Bool) (N r : ℕ),
      divQuotient128 xm ym xe ye = (zmq, zeq, dropped) ∧
      divQuotientTail zmq zeq dropped N r xm ym xe ye := by
  -- Key constant values
  have hmax_val : largeRange.max.toNat = 10 ^ 19 - 1 := by decide
  have hmin_val : largeRange.min.toNat = 10 ^ 18 := by decide
  -- UInt128 <-> Nat bridge
  have hym_nat : (toUInt128 ym).toNat = ym.toNat := toNat_toUInt128 ym
  -- numerator doesn't overflow UInt128
  have hxm_bound : xm.toNat ≤ 10 ^ 19 - 1 := by omega
  have hnum_overflow : xm.toNat * 10 ^ 17 < 2 ^ 128 := by
    calc xm.toNat * 10 ^ 17 ≤ (10 ^ 19 - 1) * 10 ^ 17 := Nat.mul_le_mul_right _ hxm_bound
      _ < 2 ^ 128 := by norm_num
  have hnum_nat : (toUInt128 xm * (100000000000000000 : UInt128)).toNat
      = xm.toNat * 10 ^ 17 := by
    have hf : ((100000000000000000 : UInt128)).toNat = 10 ^ 17 := by decide
    rw [BitVec.toNat_mul_of_lt (by rw [toNat_toUInt128, hf]; exact hnum_overflow),
        toNat_toUInt128, hf]
  -- Nat-level Euclidean division
  have hzm_nat : (toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym).toNat
      = (xm.toNat * 10 ^ 17) / ym.toNat := by
    rw [BitVec.toNat_udiv, hnum_nat, hym_nat]
  have hrem_nat : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym).toNat
      = (xm.toNat * 10 ^ 17) % ym.toNat := by
    rw [BitVec.toNat_umod, hnum_nat, hym_nat]
  have heuc : ym.toNat * ((xm.toNat * 10 ^ 17) / ym.toNat)
      + (xm.toNat * 10 ^ 17) % ym.toNat = xm.toNat * 10 ^ 17 := Nat.div_add_mod _ _
  have hrem_lt : (xm.toNat * 10 ^ 17) % ym.toNat < ym.toNat := Nat.mod_lt _ hym_pos
  -- Bounds
  have hym_lower : 10 ^ 18 ≤ ym.toNat := by omega
  have hzm_bound : (xm.toNat * 10 ^ 17) / ym.toNat ≤ 999999999999999999 := by
    calc (xm.toNat * 10 ^ 17) / ym.toNat
        ≤ (xm.toNat * 10 ^ 17) / (10 ^ 18) := Nat.div_le_div_left hym_lower (by norm_num)
      _ ≤ ((10 ^ 19 - 1) * 10 ^ 17) / (10 ^ 18) :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ hxm_bound)
      _ = 999999999999999999 := by norm_num
  -- Unfold and zeta-expand the staged body, one let per step.
  -- Case split on the Stage-1 remainder.
  by_cases hrem : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym != 0) = true
  · ---- Case: remainder != 0, Stage-2 refinement ----
    have hrem_ne_nat : (xm.toNat * 10 ^ 17) % ym.toNat ≠ 0 := by
      intro h
      exact (bne_iff_ne.mp hrem) (by rw [BitVec.toNat_eq, hrem_nat, h]; rfl)
    have hcf_val : ((100000 : UInt128)).toNat = 10 ^ 5 := by decide
    -- Overflow bound for the partial numerator
    have hrem_bound : (xm.toNat * 10 ^ 17) % ym.toNat ≤ 10 ^ 19 - 2 := by omega
    have hpn_overflow : (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 < 2 ^ 128 := by
      calc (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 ≤ (10 ^ 19 - 2) * 10 ^ 5 :=
            Nat.mul_le_mul_right _ hrem_bound
        _ < 2 ^ 128 := by norm_num
    have hpn_nat : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
        * (100000 : UInt128)).toNat = (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 := by
      rw [BitVec.toNat_mul_of_lt (by rw [hrem_nat, hcf_val]; exact hpn_overflow),
          hrem_nat, hcf_val]
    have hcorr_nat : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
        * (100000 : UInt128) / toUInt128 ym).toNat
        = (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 / ym.toNat := by
      rw [BitVec.toNat_udiv, hpn_nat, hym_nat]
    have hmod_nat : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
        * (100000 : UInt128) % toUInt128 ym).toNat
        = (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 % ym.toNat := by
      rw [BitVec.toNat_umod, hpn_nat, hym_nat]
    by_cases hcorr : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
        * (100000 : UInt128) / toUInt128 ym != 0) = true
    · ---- Sub-case: correction != 0, N = 22 ----
      rw [divQuotient128_eq_corr_ne xm ym xe ye hrem hcorr]
      -- The corrected quotient and its components stay below 2^128.
      have hcorr_bound : (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 / ym.toNat < 10 ^ 5 := by
        apply Nat.div_lt_of_lt_mul
        calc (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 < ym.toNat * 10 ^ 5 :=
              Nat.mul_lt_mul_of_pos_right hrem_lt (by norm_num : 0 < 10 ^ 5)
          _ = ym.toNat * (1 * 10 ^ 5) := by ring_nf
      have hzm_mul_overflow : (xm.toNat * 10 ^ 17) / ym.toNat * 10 ^ 5 < 2 ^ 128 := by
        calc (xm.toNat * 10 ^ 17) / ym.toNat * 10 ^ 5 ≤ 999999999999999999 * 10 ^ 5 :=
              Nat.mul_le_mul_right _ hzm_bound
          _ < 2 ^ 128 := by norm_num
      have hzm_mul_nat : (toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym
          * (100000 : UInt128)).toNat = (xm.toNat * 10 ^ 17) / ym.toNat * 10 ^ 5 := by
        rw [BitVec.toNat_mul_of_lt (by rw [hzm_nat, hcf_val]; exact hzm_mul_overflow),
            hzm_nat, hcf_val]
      have hsum_overflow : (xm.toNat * 10 ^ 17) / ym.toNat * 10 ^ 5 +
          (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 / ym.toNat < 2 ^ 128 := by
        calc (xm.toNat * 10 ^ 17) / ym.toNat * 10 ^ 5
              + (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 / ym.toNat
            < (xm.toNat * 10 ^ 17) / ym.toNat * 10 ^ 5 + 10 ^ 5 := by
              refine Nat.add_lt_add_left ((Nat.div_lt_iff_lt_mul hym_pos).mpr ?_) _
              calc (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5
                  < ym.toNat * 10 ^ 5 := (Nat.mul_lt_mul_right (by norm_num)).mpr hrem_lt
                _ = 10 ^ 5 * ym.toNat := by ring
          _ ≤ 999999999999999999 * 10 ^ 5 + 10 ^ 5 := by
              apply Nat.add_le_add_right; exact Nat.mul_le_mul_right _ hzm_bound
          _ < 2 ^ 128 := by norm_num
      have hsum_nat : (toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym
          * (100000 : UInt128)
          + toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128)
              / toUInt128 ym).toNat =
          (xm.toNat * 10 ^ 17) / ym.toNat * 10 ^ 5
            + (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 / ym.toNat := by
        rw [BitVec.toNat_add, hzm_mul_nat, hcorr_nat]
        exact Nat.mod_eq_of_lt hsum_overflow
      -- Second Euclidean division: remainder * 10^5 = q2 * ym + r2
      have heuc2 : ym.toNat * ((xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 / ym.toNat) +
          (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 % ym.toNat
          = (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 :=
        Nat.div_add_mod _ _
      refine ⟨toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym * (100000 : UInt128)
                + toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
                    * (100000 : UInt128) / toUInt128 ym,
              xe - ye - 17 - 5,
              (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128)
                % toUInt128 ym != 0),
              22, (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 % ym.toNat,
              rfl, Or.inr rfl, ?_, Nat.mod_lt _ hym_pos, ?_, ?_,
              by intro h; exact absurd h (by norm_num)⟩
      · -- Main equation: xm * 10^22 = zm_final * ym + r_final
        rw [hsum_nat, show (10 : ℕ) ^ 22 = 10 ^ 17 * 10 ^ 5 from by norm_num]
        nlinarith [heuc, heuc2]
      · -- Exponent: ze = xe - ye - 22
        push_cast; ring
      · -- Sticky flag: dropped ↔ r₂ ≠ 0
        constructor
        · intro h hr0
          exact (bne_iff_ne.mp h) (by rw [BitVec.toNat_eq, hmod_nat, hr0]; rfl)
        · intro hr
          rw [bne_iff_ne]
          intro h0
          apply hr
          rw [← hmod_nat, h0]
          rfl
    · ---- Sub-case: correction = 0, N = 17 with a tiny nonzero residual ----
      rw [divQuotient128_eq_corr_zero xm ym xe ye hrem hcorr]
      have hcorr_zero_nat : (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 / ym.toNat = 0 := by
        have h0 : toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
            * (100000 : UInt128) / toUInt128 ym = 0 := by
          by_contra hne
          exact hcorr (bne_iff_ne.mpr hne)
        rw [← hcorr_nat, h0]
        rfl
      have hpn_lt : (xm.toNat * 10 ^ 17) % ym.toNat * 10 ^ 5 < ym.toNat := by
        by_contra hge
        push Not at hge
        have := Nat.div_pos hge hym_pos
        omega
      refine ⟨toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym, xe - ye - 17,
              (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym * (100000 : UInt128)
                % toUInt128 ym != 0),
              17, (xm.toNat * 10 ^ 17) % ym.toNat,
              rfl, Or.inl rfl, ?_, hrem_lt, ?_, ?_, fun _ => hpn_lt⟩
      · -- xm * 10^17 = zm_init * ym + remainder
        rw [hzm_nat]
        linarith [heuc]
      · -- Exponent: ze = xe - ye - 17
        push_cast; ring
      · -- Sticky flag: dropped = true and remainder ≠ 0
        have hdropped : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
            * (100000 : UInt128) % toUInt128 ym != 0) = true := by
          rw [bne_iff_ne]
          intro h0
          have hh : (toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym
              * (100000 : UInt128) % toUInt128 ym).toNat = 0 := by rw [h0]; rfl
          rw [hmod_nat, Nat.mod_eq_of_lt hpn_lt] at hh
          omega
        exact ⟨fun _ => hrem_ne_nat, fun _ => hdropped⟩
  · ---- Case: remainder = 0, no refinement, N = 17 ----
    rw [divQuotient128_eq_rem_zero xm ym xe ye hrem]
    have hrem_nat_zero : (xm.toNat * 10 ^ 17) % ym.toNat = 0 := by
      have h0 : toUInt128 xm * (100000000000000000 : UInt128) % toUInt128 ym = 0 := by
        by_contra hne
        exact hrem (bne_iff_ne.mpr hne)
      rw [← hrem_nat, h0]
      rfl
    refine ⟨toUInt128 xm * (100000000000000000 : UInt128) / toUInt128 ym, xe - ye - 17,
            false, 17, 0,
            rfl, Or.inl rfl, ?_, hym_pos, ?_, ?_, fun _ => by simpa using hym_pos⟩
    · -- xm * 10^17 = zm_init * ym
      rw [hzm_nat, Nat.add_zero,
          Nat.mul_comm (xm.toNat * 10 ^ 17 / ym.toNat) ym.toNat]
      omega
    · -- Exponent: ze = xe - ye - 17
      push_cast; ring
    · -- Sticky flag: both sides false
      exact ⟨fun h => absurd h (by decide), fun h => absurd rfl h⟩

end XRPL.Model.Protocol
