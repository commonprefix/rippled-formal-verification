import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType

/-! # Basic facts

Generic facts about `ℚ`, `ℤ`, `Int64` and `Except` used by the vault proofs. -/

namespace XRPL.Model.Protocol

lemma pure_ok {α} (a : α) : (pure a : Except Error α) = .ok a := rfl

/-- The two modeled integral asset types both fit `maxRep`. -/
lemma NumericType.maxValue_le_maxRep_of_real (nt : NumericType)
    (hnt : nt = .int64 ∨ nt = .native) :
    nt.maxValue.toNat ≤ maxRep.toNat := by
  rcases hnt with h | h <;> rw [h] <;> decide

/-- Rational floor of a natural division. -/
lemma Int.floor_nat_div (a b : ℕ) (hb : 0 < b) :
    ⌊(a : ℚ) / (b : ℚ)⌋ = ((a / b : ℕ) : ℤ) := by
  have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hbq]
    exact_mod_cast Nat.div_mul_le_self a b
  · rw [div_lt_iff₀ hbq]
    have hlt : a < (a / b + 1) * b := by
      have hdm := Nat.div_add_mod a b
      have hmod := Nat.mod_lt a hb
      calc a = b * (a / b) + a % b := hdm.symm
        _ < b * (a / b) + b := by omega
        _ = (a / b + 1) * b := by ring
    exact_mod_cast hlt

/-- `Int64 → UInt64` is a bit-cast, so it sends only zero to zero. -/
lemma Int64.toUInt64_eq_zero_iff (x : Int64) : x.toUInt64 = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact Int64.toBitVec_inj.mp (congrArg UInt64.toBitVec h)
  · intro h; rw [h]; rfl

/-- Negation on `Int64` fixes only zero. -/
lemma Int64.neg_eq_zero_iff (x : Int64) : -x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hb : (-x).toBitVec = (0 : Int64).toBitVec := congrArg Int64.toBitVec h
    rw [Int64.toBitVec_neg] at hb
    have hx : x.toBitVec = 0 := by
      have := congrArg (fun b => -b) hb
      simpa using this
    exact Int64.toBitVec_inj.mp hx
  · intro h; rw [h]; rfl

/-- The sum of two integer-valued rationals is integer-valued. -/
lemma Rat.den_one_add (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) : (a + b).den = 1 := by
  have haq : a = (a.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den a]
    rw [ha]; simp
  have hbq : b = (b.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den b]
    rw [hb]; simp
  rw [haq, hbq, ← Int.cast_add]
  exact Rat.den_intCast _

/-- Numerator magnitude bound of an integer-valued rational. -/
lemma Rat.num_natAbs_lt_of_abs_le (q : ℚ) (hden : q.den = 1)
    (h : |q| ≤ (2 : ℚ) ^ 63 - 1) : q.num.natAbs < 2 ^ 63 := by
  have hq : q = (q.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    rw [hden]; simp
  have habs : |(q.num : ℚ)| ≤ (2 : ℚ) ^ 63 - 1 := by rw [← hq]; exact h
  have : (|q.num| : ℚ) ≤ (2 : ℚ) ^ 63 - 1 := by exact_mod_cast habs
  have hle : |q.num| ≤ (2 : ℤ) ^ 63 - 1 := by exact_mod_cast this
  rw [Int.abs_eq_natAbs] at hle
  omega

/-- `tryCatch` on a success runs no handler, definitional. -/
lemma tryCatch_ok {ε α} (a : α) (h : ε → Except ε α) :
    (tryCatch (Except.ok a : Except ε α) h) = .ok a := rfl

/-- `Except` `pure` is `Except.ok`, definitional. Normalizes the do-elaborated
`pure`s so the `bind`/`tryCatch` `.ok` lemmas fire. -/
lemma epure {ε α} (a : α) : (pure a : Except ε α) = Except.ok a := rfl

/-- `Except` `throw` is `Except.error`, definitional. -/
lemma ethrow {ε α} (e : ε) : (throw e : Except ε α) = Except.error e := rfl

/-- Peel one decimal digit of an `emod` by a power of ten. -/
lemma int_emod_pow10_succ (x : ℤ) (m : ℕ) :
    x % 10 ^ (m + 1) = x % 10 + 10 * ((x / 10) % 10 ^ m) := by
  have hpm : (10 : ℤ) ^ (m + 1) = 10 * 10 ^ m := by ring
  have hpos : (0 : ℤ) < 10 ^ m := by positivity
  have hr10 : 0 ≤ x % 10 ∧ x % 10 < 10 :=
    ⟨Int.emod_nonneg x (by norm_num), Int.emod_lt_of_pos x (by norm_num)⟩
  have hrm : 0 ≤ (x / 10) % 10 ^ m ∧ (x / 10) % 10 ^ m < 10 ^ m :=
    ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ hpos⟩
  have hdecomp : x = (x % 10 + 10 * ((x / 10) % 10 ^ m)) + 10 * 10 ^ m * ((x / 10) / 10 ^ m) := by
    have e1 : 10 * (x / 10) + x % 10 = x := Int.mul_ediv_add_emod x 10
    have e2 : 10 ^ m * ((x / 10) / 10 ^ m) + (x / 10) % 10 ^ m = x / 10 :=
      Int.mul_ediv_add_emod (x / 10) (10 ^ m)
    linear_combination -e1 - 10 * e2
  rw [hpm]
  conv_lhs => rw [hdecomp]
  rw [Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by nlinarith [hrm.1, hrm.2, hr10.2, hpos])]

end XRPL.Model.Protocol
