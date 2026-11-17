import XRPL.Properties.Protocol.STAmount.Common.OfNumberBoundary
import XRPL.Properties.Protocol.STAmount.Common.RoundsUp

/-! # `Number.to_rep` on a Number that may not be normalized

`STAmount.checked` on XRP or MPT turns the mantissa and exponent into a Number without normalizing it and rounds
it to an integer with `Number.to_rep`. `Number.to_rep_unchecked_eq` gives the result for both signs and every
mode: the whole part of `m * 10^e`, plus one when the mode rounds up, or an error when that is above `maxRep`. -/

namespace XRPL.Model.Protocol

/-- `growSpec` multiplies by `10^off` when the product fits `maxRep`, and fails with an overflow error when it
does not. -/
lemma growSpec_cases (D : Int64) (off : Int) (h0 : 0 < D.toInt) (hle : D.toInt ≤ (maxRep.toNat : ℤ)) :
    (D.toInt * 10 ^ off.toNat ≤ (maxRep.toNat : ℤ) →
      ∃ D' : Int64, growSpec D off = .ok D' ∧ D'.toInt = D.toInt * 10 ^ off.toNat) ∧
    ((maxRep.toNat : ℤ) < D.toInt * 10 ^ off.toNat → growSpec D off = .error .overflow) := by
  have h63 : (maxRep.toNat : ℤ) = 9223372036854775807 := by decide
  induction D, off using growSpec.induct with
  | case1 drops offset hpos hover =>
    rw [growSpec, if_pos hpos, if_pos hover]
    have hgt : (maxRep.toNat : ℤ) / 10 < drops.toInt := by
      have h := Int64.lt_iff_toInt_lt.mp hover
      rwa [show (maxRep.toInt64 / 10).toInt = (maxRep.toNat : ℤ) / 10 from by decide] at h
    have hpow : (10 : ℤ) ≤ 10 ^ offset.toNat := by
      calc (10 : ℤ) = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ offset.toNat := pow_le_pow_right₀ (by norm_num) (by omega)
    refine ⟨fun h => ?_, fun _ => rfl⟩
    exfalso
    have hmul : drops.toInt * 10 ≤ drops.toInt * 10 ^ offset.toNat := mul_le_mul_of_nonneg_left hpow h0.le
    omega
  | case2 drops offset hpos hover ih =>
    rw [growSpec, if_pos hpos, if_neg hover]
    have hguard : drops.toInt ≤ (maxRep.toNat : ℤ) / 10 := by
      have hle' : drops ≤ maxRep.toInt64 / 10 := Int64.not_lt.mp hover
      have hb : (maxRep.toInt64 / 10).toInt = (maxRep.toNat : ℤ) / 10 := by decide
      have := Int64.le_iff_toInt_le.mp hle'
      rwa [hb] at this
    have hmul := toInt_mul_ten_of_le drops h0.le hguard
    have ih' := ih (by rw [hmul]; omega) (by rw [hmul]; omega)
    have hoff : offset.toNat = (offset - 1).toNat + 1 := by omega
    have heq : (drops * 10).toInt * 10 ^ (offset - 1).toNat = drops.toInt * 10 ^ offset.toNat := by
      rw [hmul, hoff, pow_succ]
      ring
    rw [heq] at ih'
    exact ih'
  | case3 drops offset hnpos =>
    rw [growSpec, if_neg hnpos]
    have hoff : offset.toNat = 0 := by omega
    rw [hoff, pow_zero, mul_one]
    exact ⟨fun _ => ⟨drops, rfl, rfl⟩, fun h => absurd hle (not_le.mpr h)⟩

/-- `to_rep` on a Number that may not be normalized, with a mantissa within `maxRep`. The size `m * 10^e` splits
into a whole part `q` and a fraction `f`. The result is `±q` or `±(q + 1)`, or an error when that is too large. -/
lemma Number.to_rep_unchecked_eq (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode)
    (hm : m.toNat ≤ maxRep.toNat) :
    ∃ (q : ℤ) (f : ℚ) (up : Bool), 0 ≤ q ∧ 0 ≤ f ∧ f < 1 ∧
      (m.toNat : ℚ) * 10 ^ e = (q : ℚ) + f ∧
      (up = true ↔ RoundsUp mode neg q f) ∧
      (q + (if up = true then 1 else 0) ≤ (maxRep.toNat : ℤ) →
        ∃ r : Int64, (Number.unchecked neg m e).to_rep mode = .ok r ∧
          r.toInt = (if neg = true then -1 else 1) * (q + (if up = true then 1 else 0))) ∧
      ((maxRep.toNat : ℤ) < q + (if up = true then 1 else 0) →
        ∃ err, (Number.unchecked neg m e).to_rep mode = .error err) := by
  have h63 : maxRep.toNat = 2 ^ 63 - 1 := by decide
  have hmaxlt : m.toNat < 2 ^ 63 := by omega
  have hnpre : ¬ (maxRep < m) := by rw [UInt64.lt_iff_toNat_lt]; omega
  have hmant : (Number.unchecked neg m e).mantissa = (if neg then -m.toInt64 else m.toInt64) := by
    simp only [Number.mantissa, Number.unchecked, gt_iff_lt, if_neg hnpre]
  have hexp : (Number.unchecked neg m e).exponent = e := by
    simp only [Number.exponent, Number.unchecked, gt_iff_lt, if_neg hnpre]
  have hneg_ : (Number.unchecked neg m e).negative_ = neg := rfl
  have hmi : m.toInt64.toInt = (m.toNat : ℤ) := UInt64.toInt64_toInt_of_lt m hmaxlt
  have hnn : 0 ≤ m.toInt64.toInt := by rw [hmi]; positivity
  have hsign : ∀ X : Int64, 0 ≤ X.toInt →
      (if neg then -X else X).toInt = (if neg = true then -1 else 1) * X.toInt := by
    intro X hX
    cases neg
    · simp
    · simp only [if_true]
      rw [toInt_neg_of_nonneg X hX]
      ring
  have hspec : (Number.unchecked neg m e).to_rep mode = (Number.unchecked neg m e).to_repSpec mode :=
    Number.to_rep_eq_spec _ _
  unfold Number.to_repSpec at hspec
  simp only [hmant, hexp, hneg_] at hspec
  by_cases hz : (if neg then -m.toInt64 else m.toInt64) == 0
  · -- zero mantissa
    rw [if_pos hz] at hspec
    rw [beq_iff_eq] at hz
    have hm0 : m.toNat = 0 := by
      have h : (if neg then -m.toInt64 else m.toInt64).toInt = (0 : Int64).toInt :=
        congrArg Int64.toInt hz
      rw [signed_mantissa_toInt neg m hmaxlt, show (0 : Int64).toInt = 0 from by decide] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · cases neg <;> simp at h1
      · exact_mod_cast h1
    refine ⟨0, 0, false, le_refl _, le_refl _, by norm_num, by simp [hm0],
      ⟨fun h => absurd h (by decide), fun h => absurd h (not_roundsUp_zero mode neg 0)⟩,
      fun _ => ⟨0, hspec, by simp⟩, fun h => ?_⟩
    simp only [Bool.false_eq_true, if_false, add_zero] at h
    omega
  · rw [if_neg hz] at hspec
    have hm_pos : 0 < m.toNat := by
      by_contra h0
      have hm_zero : m = 0 := UInt64.toNat_inj.mp (by simp only [UInt64.toNat_zero]; omega)
      subst hm_zero
      exact hz (by cases neg <;> rfl)
    have hmag : (if neg then -(if neg then -m.toInt64 else m.toInt64)
        else (if neg then -m.toInt64 else m.toInt64)) = m.toInt64 := by
      cases neg <;> simp
    rw [hmag] at hspec
    by_cases he : e < 0
    · -- negative exponent: digits are dropped into the guard
      rw [if_pos he, if_neg (by omega : ¬ e ≥ 0)] at hspec
      simp only at hspec
      set g0 : Guard := if neg then Guard.new.set_negative else Guard.new with hg0
      set sp := shiftSpec m.toInt64 e g0 with hsp
      set k : ℕ := (-e).toNat with hk
      have hk_pos : 1 ≤ k := by omega
      have hsbit : sp.2.sbit_ = neg := by
        rw [hsp, Number.to_rep_shift_sbit, hg0]; cases neg <;> rfl
      have hq : sp.1.toInt = (m.toNat : ℤ) / 10 ^ k := by
        rw [hsp, shift_fst_eq m.toInt64 e g0 hnn, hmi]
      have hq_nn : 0 ≤ sp.1.toInt := by
        rw [hq]; exact Int.ediv_nonneg (by positivity) (by positivity)
      have hq_lt : sp.1.toInt < (maxRep.toNat : ℤ) := by
        have hmul : sp.1.toInt * 10 ^ k ≤ (m.toNat : ℤ) := by
          rw [hq]; exact Int.ediv_mul_le _ (by positivity)
        have h10le : (10 : ℤ) ≤ 10 ^ k := by
          calc (10 : ℤ) = 10 ^ 1 := by norm_num
            _ ≤ 10 ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
        have hmul10 : sp.1.toInt * 10 ≤ (m.toNat : ℤ) :=
          le_trans (mul_le_mul_of_nonneg_left h10le hq_nn) hmul
        omega
      have hpk : (0 : ℚ) < (10 : ℚ) ^ k := by positivity
      have hrep : represents sp.2 ((((m.toNat : ℤ) % 10 ^ k : ℤ) : ℚ) / 10 ^ k) := by
        have h := Number.to_rep_shift_represents m.toInt64 e g0 hnn 0 (g0_represents_zero neg)
        rw [← hsp, ← hk, hmi] at h
        simpa using h
      set f : ℚ := (((m.toNat : ℤ) % 10 ^ k : ℤ) : ℚ) / 10 ^ k with hf
      have hmod0 : (0 : ℤ) ≤ (m.toNat : ℤ) % 10 ^ k := Int.emod_nonneg _ (by positivity)
      have hmod1 : (m.toNat : ℤ) % 10 ^ k < 10 ^ k := Int.emod_lt_of_pos _ (by positivity)
      have hf0 : 0 ≤ f := by
        rw [hf]
        exact div_nonneg (Int.cast_nonneg hmod0) hpk.le
      have hf1 : f < 1 := by
        rw [hf, div_lt_one hpk]
        have h : (((m.toNat : ℤ) % 10 ^ k : ℤ) : ℚ) < ((10 ^ k : ℤ) : ℚ) := Int.cast_lt.mpr hmod1
        rwa [Int.cast_pow, Int.cast_ofNat] at h
      have hval : (m.toNat : ℚ) * 10 ^ e = ((sp.1.toInt : ℤ) : ℚ) + f := by
        have hpow : (10 : ℚ) ^ e = ((10 : ℚ) ^ k)⁻¹ := by
          rw [show e = -(k : ℤ) from by omega, zpow_neg, zpow_natCast]
        have hd : ((m.toNat : ℤ) : ℚ)
            = 10 ^ k * (((m.toNat : ℤ) / 10 ^ k : ℤ) : ℚ) + (((m.toNat : ℤ) % 10 ^ k : ℤ) : ℚ) := by
          exact_mod_cast (Int.mul_ediv_add_emod (m.toNat : ℤ) (10 ^ k)).symm
        rw [hpow, hq, hf]
        push_cast at hd ⊢
        field_simp
        linear_combination hd
      have hround := Guard.round_bool_iff hrep mode (sp.1 % 2 == 1) sp.1.toInt
        (Int64.mod_two_beq_one_iff sp.1 hq_nn)
      rw [hsbit] at hround
      have hno_ovf : ¬ sp.1 ≥ maxRep.toInt64 := by
        intro hc
        have := Int64.le_iff_toInt_le.mp hc
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
        omega
      by_cases hb : (sp.2.round mode == 1 || sp.2.round mode == 0 && sp.1 % 2 == 1) = true
      · -- one is added
        rw [if_pos hb, if_neg hno_ovf] at hspec
        have hadd : (sp.1 + 1).toInt = sp.1.toInt + 1 := by
          rw [Int64.toInt_add, int64_one_toInt, Int.bmod_eq_iff (by norm_num)]
          refine ⟨by omega, by push_cast; omega⟩
        refine ⟨sp.1.toInt, f, true, hq_nn, hf0, hf1, hval, ⟨fun _ => hround.mp hb, fun _ => rfl⟩,
          fun _ => ⟨_, hspec, ?_⟩, fun h => ?_⟩
        · rw [hsign _ (by rw [hadd]; omega), hadd]
          simp
        · simp only [if_true] at h
          omega
      · -- the whole part is kept
        rw [if_neg hb] at hspec
        refine ⟨sp.1.toInt, f, false, hq_nn, hf0, hf1, hval,
          ⟨fun h => absurd h (by decide), fun h => absurd (hround.mpr h) hb⟩,
          fun _ => ⟨_, hspec, ?_⟩, fun h => ?_⟩
        · rw [hsign _ hq_nn]
          simp
        · simp only [Bool.false_eq_true, if_false, add_zero] at h
          omega
    · -- exponent at least zero: the mantissa grows by an exact power of ten
      rw [if_neg he, if_pos (by omega : e ≥ 0)] at hspec
      obtain ⟨hgrow_ok, hgrow_err⟩ := growSpec_cases m.toInt64 e (by rw [hmi]; omega) (by rw [hmi]; omega)
      rw [hmi] at hgrow_ok hgrow_err
      refine ⟨(m.toNat : ℤ) * 10 ^ e.toNat, 0, false, by positivity, le_refl _, by norm_num, ?_,
        ⟨fun h => absurd h (by decide), fun h => absurd h (not_roundsUp_zero mode neg _)⟩, fun h => ?_,
        fun h => ?_⟩
      · push_cast
        rw [add_zero, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      · simp only [Bool.false_eq_true, if_false, add_zero] at h ⊢
        obtain ⟨D, hgrow, hD⟩ := hgrow_ok h
        rw [hgrow] at hspec
        simp only at hspec
        rw [start_guard_round] at hspec
        rw [if_neg (show ¬ ((-2 : Int) == 1 || (-2 : Int) == 0 && D % 2 == 1) = true from by simp)] at hspec
        refine ⟨_, hspec, ?_⟩
        rw [hsign D (by rw [hD]; positivity), hD]
      · simp only [Bool.false_eq_true, if_false, add_zero] at h
        rw [hgrow_err h] at hspec
        exact ⟨_, hspec⟩

end XRPL.Model.Protocol
