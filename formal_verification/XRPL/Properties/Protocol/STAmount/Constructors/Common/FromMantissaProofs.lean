import XRPL.Properties.Protocol.STAmount.Common.ToRepUnchecked
import XRPL.Properties.Protocol.STAmount.Add.Common.Integral

/-! # Proofs for an XRP or MPT amount made from a mantissa and an exponent

`STAmount.checked` on XRP or MPT turns the mantissa and exponent into a Number without normalizing it and rounds
it to an integer with `Number.to_rep`. The lemmas here follow `to_rep` on such a Number, for both signs. -/

namespace XRPL.Model.Protocol

/-- `to_rep` on a Number that may not be normalized, with a mantissa within `maxRep`. The size `m * 10^e` splits
into a whole part `q` and a dropped fraction `f`, and the result is `q` or `q + 1` with the sign put back. -/
lemma Number.to_rep_unchecked_shape (neg : Bool) (m : UInt64) (e : Int) (mode : rounding_mode) (r : Int64)
    (hm : m.toNat ≤ maxRep.toNat)
    (hok : (Number.unchecked neg m e).to_rep mode = .ok r) :
    ∃ (q : ℤ) (f : ℚ) (up : Bool), 0 ≤ f ∧ f < 1 ∧
      (m.toNat : ℚ) * 10 ^ e = (q : ℚ) + f ∧
      (r.toInt : ℚ) = (if neg = true then (-1 : ℚ) else 1) * ((q : ℚ) + (if up = true then 1 else 0)) ∧
      (up = true → f ≠ 0) ∧
      (mode = .upward → neg = false → f ≠ 0 → up = true) ∧
      (mode = .upward → neg = true → up = false) ∧
      (mode = .downward → neg = true → f ≠ 0 → up = true) ∧
      (mode = .downward → neg = false → up = false) := by
  obtain ⟨q, f, up, -, hf0, hf1, hval, hup, hfits, herr⟩ := Number.to_rep_unchecked_eq neg m e mode hm
  -- the conversion returned a result, so the rounded whole part fits
  have hfit : q + (if up = true then 1 else 0) ≤ (maxRep.toNat : ℤ) := by
    by_contra hc
    obtain ⟨err, herr'⟩ := herr (by omega)
    rw [herr'] at hok
    exact absurd hok (by simp)
  obtain ⟨r', hr', hrv⟩ := hfits hfit
  rw [hok, Except.ok.injEq] at hr'
  subst hr'
  refine ⟨q, f, up, hf0, hf1, hval, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrv]
    push_cast
    cases neg <;> cases up <;> simp
  · intro hu hf
    exact not_roundsUp_zero mode neg q (hf ▸ hup.mp hu)
  · rintro rfl hneg hf
    exact hup.mpr ⟨hneg, lt_of_le_of_ne hf0 (Ne.symm hf)⟩
  · rintro rfl hneg
    by_contra hu
    have := (hup.mp (by simpa using hu)).1
    rw [hneg] at this
    exact absurd this (by decide)
  · rintro rfl hneg hf
    exact hup.mpr ⟨hneg, lt_of_le_of_ne hf0 (Ne.symm hf)⟩
  · rintro rfl hneg
    by_contra hu
    have := (hup.mp (by simpa using hu)).1
    rw [hneg] at this
    exact absurd this (by decide)

/-- A checked XRP or MPT amount is less than one away from `mantissa * 10 ^ exponent` in every mode, at or above
it in `upward` and at or below it in `downward`. -/
lemma STAmount.checked_integral_rounds (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (mode : rounding_mode) (result : STAmount) (hint : nt.isIntegral = true)
    (hexp : -20 < e) (hm : m.toNat ≤ 9223372036854775807)
    (hok : STAmount.checked nt m e neg mode = .ok result) :
    |result.toRat - (STAmount.unchecked nt m e neg).toRat| < 1 ∧
    (mode = .upward → (STAmount.unchecked nt m e neg).toRat ≤ result.toRat) ∧
    (mode = .downward → result.toRat ≤ (STAmount.unchecked nt m e neg).toRat) := by
  have hv : (STAmount.unchecked nt m e neg).toRat
      = (if neg = true then (-1 : ℚ) else 1) * ((m.toNat : ℚ) * 10 ^ e) := by
    rw [STAmount.toRat_signed]
    show (if neg = true then (-1 : ℚ) else 1) * (m.toNat : ℚ) * 10 ^ e = _
    ring
  rw [STAmount.checked] at hok
  dsimp +instances only [STAmount.unchecked, STAmount.canonicalize, STAmount.integral] at hok
  rw [ite_eq_left hint] at hok
  by_cases hz : m = 0
  · -- a zero mantissa gives the zero amount
    rw [ite_eq_left (by rw [hz]; rfl)] at hok
    have hres : result.toRat = 0 := by
      rw [← Except.ok.inj hok]
      exact STAmount.toRat_zero_aux _ rfl rfl
    have hv0 : (STAmount.unchecked nt m e neg).toRat = 0 := by
      rw [hv, hz]
      simp
    rw [hres, hv0]
    simp
  · have hkeep : ¬ (m == 0 || decide (e ≤ -20)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact fun h => h.elim hz (by omega)
    rw [ite_eq_right hkeep] at hok
    by_cases hmoff : e > nt.maxOffset
    · rw [ite_eq_left hmoff] at hok; exact absurd hok (by simp)
    rw [ite_eq_right hmoff] at hok
    simp only [IntAmount.ofNumber] at hok
    cases hr : (Number.unchecked neg m e).to_rep mode with
    | error err => rw [hr] at hok; exact absurd hok (by simp)
    | ok r =>
      rw [hr] at hok
      simp only [] at hok
      by_cases hrng : r.magnitude > nt.maxValue
      · rw [ite_eq_left hrng] at hok; exact absurd hok (by simp)
      rw [ite_eq_right hrng] at hok
      have hres : result.toRat = (r.toInt : ℚ) := by
        rw [← Except.ok.inj hok]
        exact STAmount.reconstruct_toRat nt r
      have hm' : m.toNat ≤ maxRep.toNat := by
        rw [show maxRep.toNat = 9223372036854775807 from by decide]
        exact hm
      obtain ⟨q, f, up, hf0, hf1, hval, hrq, hup, huu, hun, hdn, hdu⟩ :=
        Number.to_rep_unchecked_shape neg m e mode r hm' hr
      rw [hres, hv, hval, hrq]
      refine ⟨?_, ?_, ?_⟩
      · -- less than one away
        cases neg <;> cases up
        all_goals simp only [Bool.false_eq_true, ite_false, ite_true, one_mul, add_zero]
        all_goals rw [abs_lt]
        · constructor <;> linarith
        · have := lt_of_le_of_ne hf0 (Ne.symm (hup rfl))
          constructor <;> linarith
        · constructor <;> linarith
        · have := lt_of_le_of_ne hf0 (Ne.symm (hup rfl))
          constructor <;> linarith
      · -- upward never ends below the value
        intro hmode
        cases neg
        · simp only [Bool.false_eq_true, ite_false, one_mul]
          by_cases hf_zero : f = 0
          · rw [hf_zero]
            split <;> linarith
          · rw [huu hmode rfl hf_zero]
            simp only [ite_true]
            linarith
        · rw [hun hmode rfl]
          simp only [ite_true, Bool.false_eq_true, ite_false]
          linarith
      · -- downward never ends above the value
        intro hmode
        cases neg
        · rw [hdu hmode rfl]
          simp only [Bool.false_eq_true, ite_false, one_mul]
          linarith
        · simp only [ite_true]
          by_cases hf_zero : f = 0
          · rw [hf_zero]
            split <;> linarith
          · rw [hdn hmode rfl hf_zero]
            simp only [ite_true]
            linarith

/-- Proof of `STAmount.checked_integral_within_one`. -/
lemma STAmount.checked_integral_within_one_proof (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (mode : rounding_mode) (result : STAmount) (hint : nt.isIntegral = true)
    (hexp : -20 < e) (hm : m.toNat ≤ 9223372036854775807)
    (hok : STAmount.checked nt m e neg mode = .ok result) :
    |result.toRat - (STAmount.unchecked nt m e neg).toRat| < 1 :=
  (STAmount.checked_integral_rounds nt m e neg mode result hint hexp hm hok).1

/-- Proof of `STAmount.checked_integral_upward`. -/
lemma STAmount.checked_integral_upward_proof (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (result : STAmount) (hint : nt.isIntegral = true)
    (hexp : -20 < e) (hm : m.toNat ≤ 9223372036854775807)
    (hok : STAmount.checked nt m e neg .upward = .ok result) :
    (STAmount.unchecked nt m e neg).toRat ≤ result.toRat :=
  (STAmount.checked_integral_rounds nt m e neg .upward result hint hexp hm hok).2.1 rfl

/-- Proof of `STAmount.checked_integral_downward`. -/
lemma STAmount.checked_integral_downward_proof (nt : NumericType) (m : UInt64) (e : Int) (neg : Bool)
    (result : STAmount) (hint : nt.isIntegral = true)
    (hexp : -20 < e) (hm : m.toNat ≤ 9223372036854775807)
    (hok : STAmount.checked nt m e neg .downward = .ok result) :
    result.toRat ≤ (STAmount.unchecked nt m e neg).toRat :=
  (STAmount.checked_integral_rounds nt m e neg .downward result hint hexp hm hok).2.2 rfl

/-- `upward` on XRP `10 * 10^-20` returns 0, because exponent -20 returns zero before rounding. -/
lemma STAmount.checked_integral_small_exponent_witness :
    STAmount.checked NumericType.native 10 (-20) false .upward = .ok ⟨NumericType.native, 0, 0, false⟩ := by
  decide +kernel

/-- Zero is below `10 * 10^-20`. -/
lemma STAmount.checked_integral_small_exponent_witness_lt :
    (⟨NumericType.native, 0, 0, false⟩ : STAmount).toRat
      < (STAmount.unchecked NumericType.native 10 (-20) false).toRat := by
  decide +kernel

/-- MPT `2^63` becomes `2^63 - 8`, because a mantissa above the largest int64 loses its last digit. -/
lemma STAmount.checked_integral_large_mantissa_witness :
    STAmount.checked NumericType.int64 9223372036854775808 0 false .to_nearest
      = .ok ⟨NumericType.int64, 9223372036854775800, 0, false⟩ := by
  decide +kernel

/-- `2^63 - 8` is 8 away from `2^63`. -/
lemma STAmount.checked_integral_large_mantissa_witness_gap :
    1 ≤ |(⟨NumericType.int64, 9223372036854775800, 0, false⟩ : STAmount).toRat
      - (STAmount.unchecked NumericType.int64 9223372036854775808 0 false).toRat| := by
  have hr : (⟨NumericType.int64, 9223372036854775800, 0, false⟩ : STAmount).toRat = 9223372036854775800 := by
    decide +kernel
  have hv : (STAmount.unchecked NumericType.int64 9223372036854775808 0 false).toRat
      = 9223372036854775808 := by
    decide +kernel
  rw [hr, hv]
  norm_num [abs_of_neg]

end XRPL.Model.Protocol
