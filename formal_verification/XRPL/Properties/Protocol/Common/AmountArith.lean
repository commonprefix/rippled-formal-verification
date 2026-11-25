import Mathlib.Tactic
import XRPL.Model.Protocol.Number

/-! # Shared `Int64`/`ℤ` arithmetic helpers for the integer amount types

`Int64` arithmetic whose exact result is in the `Int64` range does not wrap, and `Int.toInt64` gives such
values back unchanged. The file also has facts about floors and whole rational numbers. -/

namespace XRPL.Model.Protocol.AmountArith

/-- A `UInt32` is zero exactly when its natural value is. -/
lemma _root_.UInt32.toNat_eq_zero_iff (a : UInt32) : a.toNat = 0 ↔ a = 0 := by
  rw [← UInt32.toNat_inj]; rfl

/-- An integer in the `Int64` range is unchanged by `bmod 2^64`, so an `Int64` add, sub, neg or mul whose exact
result is in that range does not wrap. -/
lemma toInt_bmod_self {n : ℤ}
    (h_lo : Int64.minValue.toInt ≤ n) (h_hi : n ≤ Int64.maxValue.toInt) :
    n.bmod (2 ^ 64) = n := by
  have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
  have hmax : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
  rw [hmin] at h_lo
  rw [hmax] at h_hi
  rw [Int.bmod_eq_iff (by norm_num)]
  refine ⟨by norm_num; omega, by norm_num; omega, by simp⟩

/-- An `Int64`-range integer round-trips through `Int.toInt64`. -/
lemma toInt_toInt64_self {n : ℤ}
    (h_lo : Int64.minValue.toInt ≤ n) (h_hi : n ≤ Int64.maxValue.toInt) :
    (n.toInt64).toInt = n := by
  rw [show n.toInt64 = Int64.ofInt n from rfl, Int64.toInt_ofInt,
      show Int64.size = 2 ^ 64 from rfl, toInt_bmod_self h_lo h_hi]

end XRPL.Model.Protocol.AmountArith

namespace XRPL.Model.Protocol

/-- The sum of two whole numbers is whole. -/
lemma Rat.den_one_add (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) : (a + b).den = 1 := by
  rw [← Rat.coe_int_num_of_den_eq_one ha, ← Rat.coe_int_num_of_den_eq_one hb, ← Int.cast_add]
  exact Rat.den_intCast _

/-- The difference of two whole numbers is whole. -/
lemma Rat.den_one_sub (a b : ℚ) (ha : a.den = 1) (hb : b.den = 1) : (a - b).den = 1 := by
  rw [← Rat.coe_int_num_of_den_eq_one ha, ← Rat.coe_int_num_of_den_eq_one hb, ← Int.cast_sub]
  exact Rat.den_intCast _

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

end XRPL.Model.Protocol
