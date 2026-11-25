import XRPL.Properties.Protocol.STAmount.Common.Range
import XRPL.Properties.Protocol.STAmount.Common.RoundsUp

/-! # When a rounding step stays within a limit

`roundsWithinUnits_iff`: the rounded digits stay within a limit exactly when the exact value is inside the bounds of
the mode. `STAmount.RoundsInRange` is these bounds for the largest amount of each type. -/

namespace XRPL.Model.Protocol

/-- `v`, rounded once in the mode to a whole number of units `u`, is at most `L` units in size. -/
def RoundsWithinUnits (mode : rounding_mode) (L : ℕ) (u v : ℚ) : Prop :=
  match mode with
  | .to_nearest => |v| < ((L : ℚ) + 1 / 2) * u ∨ (|v| = ((L : ℚ) + 1 / 2) * u ∧ L % 2 = 0)
  | .towards_zero => |v| < ((L : ℚ) + 1) * u
  | .downward => -((L : ℚ) * u) ≤ v ∧ v < ((L : ℚ) + 1) * u
  | .upward => -(((L : ℚ) + 1) * u) < v ∧ v ≤ (L : ℚ) * u

/-- An XRP or MPT value is in range when it rounds to at most `maxValue` whole units. -/
lemma STAmount.roundsInRange_integral_iff (mv : UInt64) (mo : Int) (ms msh : UInt64) (mode : rounding_mode)
    (v : ℚ) :
    STAmount.RoundsInRange (.integral mv mo ms msh) mode v ↔ RoundsWithinUnits mode mv.toNat 1 v := by
  cases mode <;> simp only [STAmount.RoundsInRange, RoundsWithinUnits, mul_one]

/-- An XRP value is in range when it rounds to at most `10^17` drops. -/
lemma STAmount.roundsInRange_native_iff (mode : rounding_mode) (v : ℚ) :
    STAmount.RoundsInRange NumericType.native mode v ↔ RoundsWithinUnits mode 100000000000000000 1 v :=
  STAmount.roundsInRange_integral_iff _ _ _ _ mode v

/-- An MPT value is in range when it rounds to at most `2^63 - 1` units. -/
lemma STAmount.roundsInRange_int64_iff (mode : rounding_mode) (v : ℚ) :
    STAmount.RoundsInRange NumericType.int64 mode v ↔ RoundsWithinUnits mode 9223372036854775807 1 v :=
  STAmount.roundsInRange_integral_iff _ _ _ _ mode v

/-- An IOU value is in range when it rounds to at most `9999999999999999` units of `10^80`. -/
lemma STAmount.roundsInRange_fractional_iff (mode : rounding_mode) (v : ℚ) :
    STAmount.RoundsInRange .fractional mode v ↔
      RoundsWithinUnits mode 9999999999999999 ((10 : ℚ) ^ (80 : ℤ)) v := by
  cases mode <;> simp only [STAmount.RoundsInRange, RoundsWithinUnits] <;> norm_num

/-- The unit can be divided out of `RoundsWithinUnits`. -/
lemma roundsWithinUnits_mul_unit (mode : rounding_mode) (L : ℕ) (u x : ℚ) (hu : 0 < u) :
    RoundsWithinUnits mode L u (x * u) ↔ RoundsWithinUnits mode L 1 x := by
  cases mode
  · simp only [RoundsWithinUnits, mul_one]
    rw [abs_mul, abs_of_pos hu, mul_lt_mul_iff_left₀ hu, mul_left_inj' hu.ne']
  · simp only [RoundsWithinUnits, mul_one]
    rw [abs_mul, abs_of_pos hu, mul_lt_mul_iff_left₀ hu]
  · simp only [RoundsWithinUnits, mul_one]
    rw [← neg_mul, mul_le_mul_iff_left₀ hu, mul_lt_mul_iff_left₀ hu]
  · simp only [RoundsWithinUnits, mul_one]
    rw [← neg_mul, mul_lt_mul_iff_left₀ hu, mul_le_mul_iff_left₀ hu]

/-- A value no larger in size than `L` units is in range in every mode. -/
lemma roundsWithinUnits_of_abs_le (mode : rounding_mode) (L : ℕ) (u v : ℚ) (hu : 0 < u)
    (h : |v| ≤ (L : ℚ) * u) : RoundsWithinUnits mode L u v := by
  have hL : (0 : ℚ) ≤ (L : ℚ) := Nat.cast_nonneg L
  obtain ⟨h1, h2⟩ := abs_le.mp h
  cases mode
  · left
    show |v| < ((L : ℚ) + 1 / 2) * u
    nlinarith
  · show |v| < ((L : ℚ) + 1) * u
    nlinarith
  · exact ⟨h1, by nlinarith⟩
  · exact ⟨by nlinarith, h2⟩

/-- A value at least `L + 1` units in size is out of range in every mode. -/
lemma not_roundsWithinUnits_of_le_abs (mode : rounding_mode) (L : ℕ) (u v : ℚ) (hu : 0 < u)
    (h : ((L : ℚ) + 1) * u ≤ |v|) : ¬ RoundsWithinUnits mode L u v := by
  have hL : (0 : ℚ) ≤ (L : ℚ) := Nat.cast_nonneg L
  cases mode
  · rintro (h1 | ⟨h1, -⟩) <;> nlinarith
  · intro h1
    exact absurd (lt_of_le_of_lt h h1) (lt_irrefl _)
  · rintro ⟨h1, h2⟩
    rcases le_abs.mp h with h' | h' <;> nlinarith
  · rintro ⟨h1, h2⟩
    rcases le_abs.mp h with h' | h' <;> nlinarith

/-- The rounded digits `q` or `q + 1` are at most `L` exactly when the exact value `±(q + f)` units is inside
the bounds of the mode. -/
lemma roundsWithinUnits_iff (mode : rounding_mode) (neg : Bool) (q : ℤ) (L : ℕ) (f u : ℚ) (up : Bool)
    (hq : 0 ≤ q) (hf0 : 0 ≤ f) (hf1 : f < 1) (hu : 0 < u) (hup : up = true ↔ RoundsUp mode neg q f) :
    q + (if up = true then 1 else 0) ≤ (L : ℤ) ↔
      RoundsWithinUnits mode L u ((if neg = true then (-1 : ℚ) else 1) * ((q : ℚ) + f) * u) := by
  rw [roundsWithinUnits_mul_unit mode L u _ hu]
  have hq' : (0 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hL' : (0 : ℚ) ≤ (L : ℚ) := Nat.cast_nonneg L
  have hw : (0 : ℚ) ≤ (q : ℚ) + f := by linarith
  -- integer comparisons of `q` and `L` as rational ones
  have hle : q ≤ (L : ℤ) → (q : ℚ) ≤ (L : ℚ) := fun h => by exact_mod_cast h
  have hlt : q + 1 ≤ (L : ℤ) → (q : ℚ) + 1 ≤ (L : ℚ) := fun h => by exact_mod_cast h
  have hge : (L : ℤ) ≤ q → (L : ℚ) ≤ (q : ℚ) := fun h => by exact_mod_cast h
  have hgt : (L : ℤ) + 1 ≤ q → (L : ℚ) + 1 ≤ (q : ℚ) := fun h => by exact_mod_cast h
  have habs : |(if neg = true then (-1 : ℚ) else 1) * ((q : ℚ) + f)| = (q : ℚ) + f := by
    cases neg
    · simp only [Bool.false_eq_true, ite_false, one_mul]
      exact abs_of_nonneg hw
    · simp only [ite_true, neg_one_mul, abs_neg]
      exact abs_of_nonneg hw
  cases mode with
  | towards_zero =>
    have hno : up = false := by
      cases up
      · rfl
      · exact absurd (hup.mp rfl) (by simp [RoundsUp])
    subst hno
    simp only [RoundsWithinUnits, mul_one, habs, Bool.false_eq_true, ite_false, add_zero]
    constructor
    · intro h
      have := hle h
      linarith
    · intro h
      by_contra hc
      have := hgt (by omega)
      linarith
  | to_nearest =>
    simp only [RoundsWithinUnits, mul_one, habs]
    cases up
    · have hnp : ¬ (1 / 2 < f ∨ (f = 1 / 2 ∧ q % 2 = 1)) := fun hp => Bool.false_ne_true (hup.mpr hp)
      rw [not_or] at hnp
      obtain ⟨hf_le, hnodd⟩ := hnp
      simp only [Bool.false_eq_true, ite_false, add_zero]
      constructor
      · intro h
        rcases lt_or_eq_of_le (not_lt.mp hf_le) with hf_lt | hf_eq
        · left
          have := hle h
          linarith
        · have heven : q % 2 = 0 := by
            by_contra hne
            exact hnodd ⟨hf_eq, by omega⟩
          rcases lt_or_eq_of_le h with hql | hql
          · left
            have := hlt (by omega)
            linarith
          · right
            refine ⟨?_, by omega⟩
            have : (q : ℚ) = (L : ℚ) := by exact_mod_cast hql
            linarith
      · intro h
        by_contra hc
        have := hgt (by omega)
        rcases h with h | ⟨h, -⟩ <;> linarith
    · have hp := hup.mp rfl
      simp only [ite_true]
      constructor
      · intro h
        left
        have := hlt h
        linarith
      · intro h
        by_contra hc
        have hLq := hge (by omega)
        rcases h with h | ⟨h, heven⟩
        · rcases hp with hp | ⟨hp, -⟩ <;> linarith
        · rcases hp with hp | ⟨hp, hodd⟩
          · linarith
          · have hqL : (q : ℚ) = (L : ℚ) := by linarith
            have hqL' : q = (L : ℤ) := by exact_mod_cast hqL
            omega
  | downward =>
    cases neg
    · have hno : up = false := by
        cases up
        · rfl
        · exact absurd (hup.mp rfl) (by simp [RoundsUp])
      subst hno
      simp only [RoundsWithinUnits, mul_one, Bool.false_eq_true, ite_false, one_mul, add_zero]
      constructor
      · intro h
        have := hle h
        constructor <;> linarith
      · intro h
        by_contra hc
        have := hgt (by omega)
        linarith [h.2]
    · simp only [RoundsWithinUnits, mul_one, ite_true, neg_one_mul]
      cases up
      · have hf_zero : f = 0 := by
          by_contra hne
          exact Bool.false_ne_true (hup.mpr ⟨rfl, lt_of_le_of_ne hf0 (Ne.symm hne)⟩)
        simp only [Bool.false_eq_true, ite_false, add_zero, hf_zero]
        constructor
        · intro h
          have := hle h
          constructor <;> linarith
        · intro h
          by_contra hc
          have := hgt (by omega)
          linarith [h.1]
      · have hf_pos : 0 < f := (hup.mp rfl).2
        simp only [ite_true]
        constructor
        · intro h
          have := hlt h
          constructor <;> linarith
        · intro h
          by_contra hc
          have := hge (by omega)
          linarith [h.1]
  | upward =>
    cases neg
    · simp only [RoundsWithinUnits, mul_one, Bool.false_eq_true, ite_false, one_mul]
      cases up
      · have hf_zero : f = 0 := by
          by_contra hne
          exact Bool.false_ne_true (hup.mpr ⟨rfl, lt_of_le_of_ne hf0 (Ne.symm hne)⟩)
        simp only [Bool.false_eq_true, ite_false, add_zero, hf_zero]
        constructor
        · intro h
          have := hle h
          constructor <;> linarith
        · intro h
          by_contra hc
          have := hgt (by omega)
          linarith [h.2]
      · have hf_pos : 0 < f := (hup.mp rfl).2
        simp only [ite_true]
        constructor
        · intro h
          have := hlt h
          constructor <;> linarith
        · intro h
          by_contra hc
          have := hge (by omega)
          linarith [h.2]
    · have hno : up = false := by
        cases up
        · rfl
        · exact absurd (hup.mp rfl) (by simp [RoundsUp])
      subst hno
      simp only [RoundsWithinUnits, mul_one, ite_true, neg_one_mul, Bool.false_eq_true, ite_false, add_zero]
      constructor
      · intro h
        have := hle h
        constructor <;> linarith
      · intro h
        by_contra hc
        have := hgt (by omega)
        linarith [h.1]

end XRPL.Model.Protocol
