import Mathlib.Tactic
import XRPL.Model.Protocol.FixedWidth
import XRPL.Model.Protocol.IOUAmount
import XRPL.Properties.Protocol.Common.Reduction

/-! # Checked fixed-width operations

A checked operation gives the raw operation's result when the exact result fits its type, and `Error.wrap`
otherwise. It never fails in any other way. -/

namespace XRPL.Model.Protocol

lemma _root_.UInt32.addChecked_eq_ok {a b c : UInt32} :
    a.addChecked b = .ok c ↔ a.toNat + b.toNat < 2 ^ 32 ∧ a + b = c := by
  unfold UInt32.addChecked
  split <;> simp_all

lemma _root_.UInt32.subChecked_eq_ok {a b c : UInt32} : a.subChecked b = .ok c ↔ b ≤ a ∧ a - b = c := by
  unfold UInt32.subChecked
  split <;> simp_all

lemma _root_.Nat.toInt64Checked_eq_ok {n : Nat} {c : Int64} :
    n.toInt64Checked = .ok c ↔ n < 2 ^ 63 ∧ n.toInt64 = c := by
  unfold Nat.toInt64Checked
  split <;> simp_all

lemma _root_.Int.toInt64Checked_eq_ok {i : Int} {c : Int64} :
    i.toInt64Checked = .ok c ↔ (-9223372036854775808 ≤ i ∧ i ≤ 9223372036854775807) ∧ i.toInt64 = c := by
  unfold Int.toInt64Checked
  split <;> simp_all

lemma _root_.UInt64.toInt64Checked_eq_ok {a : UInt64} {c : Int64} :
    a.toInt64Checked = .ok c ↔ a.toNat < 2 ^ 63 ∧ a.toInt64 = c := by
  unfold UInt64.toInt64Checked
  split <;> simp_all

lemma _root_.Int64.toUInt64Checked_eq_ok {a : Int64} {c : UInt64} :
    a.toUInt64Checked = .ok c ↔ 0 ≤ a ∧ a.toUInt64 = c := by
  unfold Int64.toUInt64Checked
  split <;> simp_all

lemma _root_.Int64.negChecked_eq_ok {a c : Int64} : a.negChecked = .ok c ↔ a ≠ Int64.minValue ∧ -a = c := by
  unfold Int64.negChecked
  split <;> simp_all

lemma _root_.Int64.addChecked_eq_ok {a b c : Int64} :
    a.addChecked b = .ok c ↔
      (-9223372036854775808 ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ 9223372036854775807) ∧ a + b = c := by
  unfold Int64.addChecked
  split <;> simp_all

lemma _root_.Int64.mulChecked_eq_ok {a b c : Int64} :
    a.mulChecked b = .ok c ↔
      (-9223372036854775808 ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 9223372036854775807) ∧ a * b = c := by
  unfold Int64.mulChecked
  split <;> simp_all

lemma _root_.BitVec.addChecked_eq_ok {w : Nat} {a b c : BitVec w} :
    a.addChecked b = .ok c ↔ a.toNat + b.toNat < 2 ^ w ∧ a + b = c := by
  unfold BitVec.addChecked
  split <;> simp_all

lemma _root_.BitVec.mulChecked_eq_ok {w : Nat} {a b c : BitVec w} :
    a.mulChecked b = .ok c ↔ a.toNat * b.toNat < 2 ^ w ∧ a * b = c := by
  unfold BitVec.mulChecked
  split <;> simp_all

lemma _root_.UInt64.addChecked_eq_ok {a b c : UInt64} :
    a.addChecked b = .ok c ↔ a.toNat + b.toNat < 2 ^ 64 ∧ a + b = c := by
  unfold UInt64.addChecked
  split <;> simp_all

lemma _root_.UInt64.subChecked_eq_ok {a b c : UInt64} : a.subChecked b = .ok c ↔ b ≤ a ∧ a - b = c := by
  unfold UInt64.subChecked
  split <;> simp_all

lemma _root_.UInt64.mulChecked_eq_ok {a b c : UInt64} :
    a.mulChecked b = .ok c ↔ a.toNat * b.toNat < 2 ^ 64 ∧ a * b = c := by
  unfold UInt64.mulChecked
  split <;> simp_all

lemma toUInt64Checked_eq_ok {x : UInt128} {c : UInt64} :
    toUInt64Checked x = .ok c ↔ x.toNat < 2 ^ 64 ∧ toUInt64 x = c := by
  unfold toUInt64Checked
  split <;> simp_all

lemma _root_.BitVec.subChecked_eq_ok {w : Nat} {a b c : BitVec w} :
    a.subChecked b = .ok c ↔ b.toNat ≤ a.toNat ∧ a - b = c := by
  unfold BitVec.subChecked
  split <;> simp_all

lemma _root_.UInt32.addChecked_of_lt {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) :
    a.addChecked b = .ok (a + b) :=
  UInt32.addChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.UInt32.subChecked_of_le {a b : UInt32} (h : b ≤ a) : a.subChecked b = .ok (a - b) :=
  UInt32.subChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.Nat.toInt64Checked_of_lt {n : Nat} (h : n < 2 ^ 63) : n.toInt64Checked = .ok n.toInt64 :=
  Nat.toInt64Checked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.Int.toInt64Checked_of_bounds {i : Int} (h1 : -2 ^ 63 ≤ i) (h2 : i < 2 ^ 63) :
    i.toInt64Checked = .ok i.toInt64 :=
  Int.toInt64Checked_eq_ok.mpr ⟨⟨by omega, by omega⟩, rfl⟩

lemma _root_.UInt64.toInt64Checked_of_lt {a : UInt64} (h : a.toNat < 2 ^ 63) :
    a.toInt64Checked = .ok a.toInt64 :=
  UInt64.toInt64Checked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.Int64.toUInt64Checked_of_nonneg {a : Int64} (h : 0 ≤ a) : a.toUInt64Checked = .ok a.toUInt64 :=
  Int64.toUInt64Checked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.Int64.negChecked_of_ne {a : Int64} (h : a ≠ Int64.minValue) : a.negChecked = .ok (-a) :=
  Int64.negChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.Int64.addChecked_of_bounds {a b : Int64} (h1 : -2 ^ 63 ≤ a.toInt + b.toInt)
    (h2 : a.toInt + b.toInt < 2 ^ 63) : a.addChecked b = .ok (a + b) :=
  Int64.addChecked_eq_ok.mpr ⟨⟨by omega, by omega⟩, rfl⟩

lemma _root_.Int64.mulChecked_of_bounds {a b : Int64} (h1 : -2 ^ 63 ≤ a.toInt * b.toInt)
    (h2 : a.toInt * b.toInt < 2 ^ 63) : a.mulChecked b = .ok (a * b) :=
  Int64.mulChecked_eq_ok.mpr ⟨⟨by omega, by omega⟩, rfl⟩

lemma _root_.BitVec.addChecked_of_lt {w : Nat} {a b : BitVec w} (h : a.toNat + b.toNat < 2 ^ w) :
    a.addChecked b = .ok (a + b) :=
  BitVec.addChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.BitVec.mulChecked_of_lt {w : Nat} {a b : BitVec w} (h : a.toNat * b.toNat < 2 ^ w) :
    a.mulChecked b = .ok (a * b) :=
  BitVec.mulChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.UInt64.addChecked_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    a.addChecked b = .ok (a + b) :=
  UInt64.addChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.UInt64.subChecked_of_le {a b : UInt64} (h : b ≤ a) : a.subChecked b = .ok (a - b) :=
  UInt64.subChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.UInt64.mulChecked_of_lt {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    a.mulChecked b = .ok (a * b) :=
  UInt64.mulChecked_eq_ok.mpr ⟨h, rfl⟩

lemma toUInt64Checked_of_lt {x : UInt128} (h : x.toNat < 2 ^ 64) : toUInt64Checked x = .ok (toUInt64 x) :=
  toUInt64Checked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.BitVec.subChecked_of_le {w : Nat} {a b : BitVec w} (h : b.toNat ≤ a.toNat) :
    a.subChecked b = .ok (a - b) :=
  BitVec.subChecked_eq_ok.mpr ⟨h, rfl⟩

lemma _root_.UInt32.addChecked_eq_error {a b : UInt32} {e : Error} (h : a.addChecked b = .error e) :
    e = .wrap := by
  unfold UInt32.addChecked at h
  split at h <;> cases h; rfl

lemma _root_.UInt32.subChecked_eq_error {a b : UInt32} {e : Error} (h : a.subChecked b = .error e) :
    e = .wrap := by
  unfold UInt32.subChecked at h
  split at h <;> cases h; rfl

lemma _root_.Nat.toInt64Checked_eq_error {n : Nat} {e : Error} (h : n.toInt64Checked = .error e) :
    e = .wrap := by
  unfold Nat.toInt64Checked at h
  split at h <;> cases h; rfl

lemma _root_.Int.toInt64Checked_eq_error {i : Int} {e : Error} (h : i.toInt64Checked = .error e) : e = .wrap := by
  unfold Int.toInt64Checked at h
  split at h <;> cases h; rfl

lemma _root_.UInt64.toInt64Checked_eq_error {a : UInt64} {e : Error} (h : a.toInt64Checked = .error e) : e = .wrap := by
  unfold UInt64.toInt64Checked at h
  split at h <;> cases h; rfl

lemma _root_.Int64.toUInt64Checked_eq_error {a : Int64} {e : Error} (h : a.toUInt64Checked = .error e) : e = .wrap := by
  unfold Int64.toUInt64Checked at h
  split at h <;> cases h; rfl

lemma _root_.Int64.negChecked_eq_error {a : Int64} {e : Error} (h : a.negChecked = .error e) : e = .wrap := by
  unfold Int64.negChecked at h
  split at h <;> cases h; rfl

lemma _root_.Int64.addChecked_eq_error {a b : Int64} {e : Error} (h : a.addChecked b = .error e) : e = .wrap := by
  unfold Int64.addChecked at h
  split at h <;> cases h; rfl

lemma _root_.Int64.mulChecked_eq_error {a b : Int64} {e : Error} (h : a.mulChecked b = .error e) : e = .wrap := by
  unfold Int64.mulChecked at h
  split at h <;> cases h; rfl

lemma _root_.BitVec.addChecked_eq_error {w : Nat} {a b : BitVec w} {e : Error} (h : a.addChecked b = .error e) : e = .wrap := by
  unfold BitVec.addChecked at h
  split at h <;> cases h; rfl

lemma _root_.BitVec.mulChecked_eq_error {w : Nat} {a b : BitVec w} {e : Error} (h : a.mulChecked b = .error e) : e = .wrap := by
  unfold BitVec.mulChecked at h
  split at h <;> cases h; rfl

lemma _root_.UInt64.addChecked_eq_error {a b : UInt64} {e : Error} (h : a.addChecked b = .error e) : e = .wrap := by
  unfold UInt64.addChecked at h
  split at h <;> cases h; rfl

lemma _root_.UInt64.subChecked_eq_error {a b : UInt64} {e : Error} (h : a.subChecked b = .error e) : e = .wrap := by
  unfold UInt64.subChecked at h
  split at h <;> cases h; rfl

lemma _root_.UInt64.mulChecked_eq_error {a b : UInt64} {e : Error} (h : a.mulChecked b = .error e) : e = .wrap := by
  unfold UInt64.mulChecked at h
  split at h <;> cases h; rfl

lemma toUInt64Checked_eq_error {x : UInt128} {e : Error} (h : toUInt64Checked x = .error e) : e = .wrap := by
  unfold toUInt64Checked at h
  split at h <;> cases h; rfl

lemma _root_.BitVec.subChecked_eq_error {w : Nat} {a b : BitVec w} {e : Error} (h : a.subChecked b = .error e) : e = .wrap := by
  unfold BitVec.subChecked at h
  split at h <;> cases h; rfl

lemma _root_.UInt32.addChecked_ne_notLawful (a b : UInt32) : a.addChecked b ≠ .error .notLawful :=
  fun h => nomatch UInt32.addChecked_eq_error h

lemma _root_.UInt32.subChecked_ne_notLawful (a b : UInt32) : a.subChecked b ≠ .error .notLawful :=
  fun h => nomatch UInt32.subChecked_eq_error h

lemma _root_.Nat.toInt64Checked_ne_notLawful (n : Nat) : n.toInt64Checked ≠ .error .notLawful :=
  fun h => nomatch Nat.toInt64Checked_eq_error h

@[simp] lemma _root_.Int.toInt64Checked_ne_notLawful (i : Int) : i.toInt64Checked ≠ .error .notLawful :=
  fun h => nomatch Int.toInt64Checked_eq_error h

@[simp] lemma _root_.UInt64.toInt64Checked_ne_notLawful (a : UInt64) : a.toInt64Checked ≠ .error .notLawful :=
  fun h => nomatch UInt64.toInt64Checked_eq_error h

@[simp] lemma _root_.Int64.toUInt64Checked_ne_notLawful (a : Int64) : a.toUInt64Checked ≠ .error .notLawful :=
  fun h => nomatch Int64.toUInt64Checked_eq_error h

@[simp] lemma _root_.Int64.negChecked_ne_notLawful (a : Int64) : a.negChecked ≠ .error .notLawful :=
  fun h => nomatch Int64.negChecked_eq_error h

@[simp] lemma _root_.Int64.addChecked_ne_notLawful (a b : Int64) : a.addChecked b ≠ .error .notLawful :=
  fun h => nomatch Int64.addChecked_eq_error h

@[simp] lemma _root_.Int64.mulChecked_ne_notLawful (a b : Int64) : a.mulChecked b ≠ .error .notLawful :=
  fun h => nomatch Int64.mulChecked_eq_error h

@[simp] lemma _root_.BitVec.addChecked_ne_notLawful {w : Nat} (a b : BitVec w) : a.addChecked b ≠ .error .notLawful :=
  fun h => nomatch BitVec.addChecked_eq_error h

@[simp] lemma _root_.BitVec.mulChecked_ne_notLawful {w : Nat} (a b : BitVec w) : a.mulChecked b ≠ .error .notLawful :=
  fun h => nomatch BitVec.mulChecked_eq_error h

@[simp] lemma _root_.UInt64.addChecked_ne_notLawful (a b : UInt64) : a.addChecked b ≠ .error .notLawful :=
  fun h => nomatch UInt64.addChecked_eq_error h

@[simp] lemma _root_.UInt64.subChecked_ne_notLawful (a b : UInt64) : a.subChecked b ≠ .error .notLawful :=
  fun h => nomatch UInt64.subChecked_eq_error h

@[simp] lemma _root_.UInt64.mulChecked_ne_notLawful (a b : UInt64) : a.mulChecked b ≠ .error .notLawful :=
  fun h => nomatch UInt64.mulChecked_eq_error h

@[simp] lemma toUInt64Checked_ne_notLawful (x : UInt128) : toUInt64Checked x ≠ .error .notLawful :=
  fun h => nomatch toUInt64Checked_eq_error h

@[simp] lemma _root_.BitVec.subChecked_ne_notLawful {w : Nat} (a b : BitVec w) : a.subChecked b ≠ .error .notLawful :=
  fun h => nomatch BitVec.subChecked_eq_error h

/-- A `UInt32` other than zero is at least one. -/
lemma _root_.UInt32.one_le_of_ne_zero {a : UInt32} (h : a ≠ 0) : 1 ≤ a := by
  rw [UInt32.le_iff_toNat_le, UInt32.toNat_one]
  rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
  · exact absurd (UInt32.toNat_inj.mp (by rw [h0, UInt32.toNat_zero])) h
  · exact h0

/-- A count other than the largest `UInt32` has a successor. -/
lemma _root_.UInt32.toNat_add_one_lt {a : UInt32} (h : a + 1 ≠ 0) : a.toNat + 1 < 2 ^ 32 := by
  by_contra hc
  apply h
  have ha := a.toNat_lt
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one, UInt32.toNat_zero]
  omega

/-- A checked subtraction of a smaller value never wraps. -/
lemma _root_.UInt32.subChecked_ne_wrap_of_lt {a b : UInt32} (h : b < a) : a.subChecked b ≠ .error .wrap := by
  rw [UInt32.subChecked_of_le (UInt32.le_of_lt h)]; exact nofun

/-- The widening conversion is the two-step one the model used before. -/
lemma _root_.UInt32.toInt64_eq (a : UInt32) : a.toInt64 = a.toUInt64.toInt64 := rfl

lemma _root_.UInt32.toInt_toInt64 (a : UInt32) : a.toInt64.toInt = a.toNat := by
  have h := a.toNat_lt
  unfold UInt32.toInt64 Int64.toInt UInt64.toInt64
  change a.toUInt64.toBitVec.toInt = (a.toNat : ℤ)
  have hb : a.toUInt64.toBitVec.toNat = a.toNat := UInt32.toNat_toUInt64 a
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [hb]; omega), hb]

/-- The magnitude is the absolute value converted to `UInt64`. -/
lemma _root_.Int64.magnitude_eq (a : Int64) : a.magnitude = a.toInt.natAbs.toUInt64 := rfl

/-- The magnitude is the absolute value, which always fits. -/
lemma _root_.Int64.toNat_magnitude (a : Int64) : a.magnitude.toNat = a.toInt.natAbs := by
  have h1 := a.le_toInt
  have h2 := a.toInt_lt
  unfold Int64.magnitude
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- A non-negative `Int64` read as a `UInt64` keeps its value. -/
private lemma toUInt64_toNat_of_nonneg' (a : Int64) (h0 : 0 ≤ a.toInt) : (a.toUInt64.toNat : ℤ) = a.toInt := by
  have hsz : a.toUInt64.toNat < 2 ^ 64 := UInt64.toNat_lt_size _
  have h1 : a.toInt = a.toBitVec.toInt := rfl
  have hb : a.toBitVec.toNat = a.toUInt64.toNat := rfl
  by_cases hlt : 2 * a.toUInt64.toNat < 2 ^ 64
  · have h := BitVec.toInt_eq_toNat_of_lt (x := a.toBitVec) (by rw [hb]; omega)
    rw [h1, h, hb]
  · exfalso
    have h2 : a.toInt = Int.bmod (a.toUInt64.toNat : ℤ) (2 ^ 64) := by
      rw [h1, BitVec.toInt_eq_toNat_bmod, hb]
    rw [Int.bmod_def] at h2
    split at h2 <;> omega

/-- A non-negative `Int64` read as a `UInt64` is its magnitude. -/
lemma _root_.Int64.toUInt64_eq_magnitude {a : Int64} (h : 0 ≤ a) : a.toUInt64 = a.magnitude := by
  have h0 : 0 ≤ a.toInt := by simpa using Int64.le_iff_toInt_le.mp h
  have hc := toUInt64_toNat_of_nonneg' a h0
  apply UInt64.toNat_inj.mp
  rw [Int64.toNat_magnitude]
  omega

/-- A negative `Int64` negated and read as a `UInt64` is its magnitude, `Int64.minValue` included. -/
lemma _root_.Int64.neg_toUInt64_eq_magnitude {a : Int64} (h : a < 0) : (-a).toUInt64 = a.magnitude := by
  by_cases hmin : a = Int64.minValue
  · subst hmin; decide
  have hlt : a.toInt < 0 := by simpa using Int64.lt_iff_toInt_lt.mp h
  have hle := a.le_toInt
  have hne : a.toInt ≠ -2 ^ 63 := fun h' => hmin (Int64.toInt_inj.mp (by rw [h']; decide))
  have hneg : (-a).toInt = -a.toInt := by
    rw [Int64.toInt_neg, Int.bmod_eq_iff (by norm_num)]
    refine ⟨?_, ?_⟩ <;> push_cast <;> omega
  have hc := toUInt64_toNat_of_nonneg' (-a) (by rw [hneg]; omega)
  apply UInt64.toNat_inj.mp
  rw [Int64.toNat_magnitude]
  omega

/-- The sign-cleared IOU mantissa read as a `UInt64` is the magnitude. -/
lemma IOUAmount.absMant_toUInt64 (i : IOUAmount) :
    (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64 = i.mantissa_.magnitude := by
  unfold IOUAmount.signum
  by_cases h : i.mantissa_ < 0
  · rw [if_pos h, if_pos (by decide)]
    exact Int64.neg_toUInt64_eq_magnitude h
  · rw [if_neg h]
    have h0 : 0 ≤ i.mantissa_ := by
      rcases Int64.lt_or_le i.mantissa_ 0 with h' | h'
      · exact absurd h' h
      · exact h'
    rw [if_neg (by split <;> decide)]
    exact Int64.toUInt64_eq_magnitude h0

end XRPL.Model.Protocol
