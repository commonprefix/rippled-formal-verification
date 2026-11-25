import XRPL.Model.Protocol.STAmount
import XRPL.Properties.Protocol.Common.FixedWidth

/-! # STAmount conversions to a signed value

`intAmount`, `iou` and addition read the stored mantissa as an `Int64` through a checked conversion. It succeeds
exactly when the mantissa is below `2^63`, and then gives the `Int64` view of the signed value. -/

namespace XRPL.Model.Protocol

/-- The `Int64` view of `signedDrops` is the mantissa cast to `Int64`, negated for a negative amount. -/
lemma STAmount.signedDrops_toInt64 (s : STAmount) :
    s.signedDrops.toInt64 = if s.mIsNegative then -s.mValue.toInt64 else s.mValue.toInt64 := by
  have hpos : ((s.mValue.toNat : Int)).toInt64 = s.mValue.toInt64 := by
    apply Int64.toBitVec_inj.mp
    simp [Int.toInt64, Int64.ofInt, UInt64.toInt64]
  unfold STAmount.signedDrops
  split
  · show Int64.ofInt (-(s.mValue.toNat : Int)) = _
    rw [Int64.ofInt_neg]; congr 1
  · exact hpos

/-- The checked read succeeds exactly when the mantissa is below `2^63`, and gives the signed value. -/
lemma STAmount.signedDropsChecked_eq_ok {s : STAmount} {c : Int64} :
    s.signedDropsChecked = .ok c ↔ s.mValue.toNat < 2 ^ 63 ∧ s.signedDrops.toInt64 = c := by
  unfold STAmount.signedDropsChecked
  constructor
  · intro h
    obtain ⟨m, hm, h⟩ := bind_ok_peel _ _ _ h
    obtain ⟨hlt, rfl⟩ := UInt64.toInt64Checked_eq_ok.mp hm
    cases h
    exact ⟨hlt, STAmount.signedDrops_toInt64 s⟩
  · rintro ⟨hlt, rfl⟩
    rw [UInt64.toInt64Checked_of_lt hlt, ok_bind, STAmount.signedDrops_toInt64]; rfl

lemma STAmount.signedDropsChecked_of_lt (s : STAmount) (h : s.mValue.toNat < 2 ^ 63) :
    s.signedDropsChecked = .ok s.signedDrops.toInt64 :=
  STAmount.signedDropsChecked_eq_ok.mpr ⟨h, rfl⟩

/-- The checked read stops with the wrap error exactly when the mantissa is above the largest `Int64`. -/
lemma STAmount.signedDropsChecked_eq_wrap {s : STAmount} :
    s.signedDropsChecked = .error .wrap ↔ maxRep < s.mValue := by
  rw [UInt64.lt_iff_toNat_lt, show maxRep.toNat = 9223372036854775807 from by decide]
  unfold STAmount.signedDropsChecked UInt64.toInt64Checked
  split
  · rename_i h; simp only [ok_bind]; constructor
    · intro hc; cases hc
    · intro hc; omega
  · rename_i h; simp only [err_bind]; constructor
    · intro _; omega
    · intro _; trivial

lemma STAmount.signedDropsChecked_eq_error {s : STAmount} {e : Error} (h : s.signedDropsChecked = .error e) :
    e = .wrap := by
  unfold STAmount.signedDropsChecked at h
  rcases hm : s.mValue.toInt64Checked with e' | m
  · rw [hm, err_bind] at h; cases h; exact UInt64.toInt64Checked_eq_error hm
  · rw [hm, ok_bind] at h; cases h

@[simp] lemma STAmount.signedDropsChecked_ne_notLawful (s : STAmount) :
    s.signedDropsChecked ≠ .error .notLawful :=
  fun h => nomatch STAmount.signedDropsChecked_eq_error h

/-- `iou` of a fractional amount whose mantissa is below `2^63` normalizes the `Int64` view of its signed value. -/
lemma STAmount.iou_eq {s : STAmount} (mode : rounding_mode) (hint : ¬ s.integral = true)
    (hlt : s.mValue.toNat < 2 ^ 63) :
    s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
  unfold STAmount.iou
  rw [ite_eq_right hint, STAmount.signedDropsChecked_of_lt s hlt, ok_bind]

/-- A successful `iou` normalized the `Int64` view of the signed value. -/
lemma STAmount.iou_ok_peel {s : STAmount} {mode : rounding_mode} {i : IOUAmount} (hint : ¬ s.integral = true)
    (h : s.iou mode = .ok i) : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode = .ok i := by
  unfold STAmount.iou at h
  rw [ite_eq_right hint] at h
  obtain ⟨m, hm, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨-, rfl⟩ := STAmount.signedDropsChecked_eq_ok.mp hm
  exact h

/-- `uncheckedFromInt64` stores the magnitude and the sign of any `Int64` but the smallest. -/
lemma STAmount.uncheckedFromInt64_of_ne (nt : NumericType) {v : Int64} (o : Int) (hv : v ≠ Int64.minValue) :
    STAmount.uncheckedFromInt64 nt v o = .ok (STAmount.unchecked nt v.magnitude o (decide (v < 0))) := by
  unfold STAmount.uncheckedFromInt64
  split
  · rename_i hneg
    rw [Int64.negChecked_of_ne hv, ok_bind]
    simp only [pure, Except.pure, hneg, decide_true, Int64.neg_toUInt64_eq_magnitude hneg]
  · rename_i hneg
    simp only [hneg, decide_false, Int64.toUInt64_eq_magnitude (Int64.not_lt.mp hneg)]

/-- A successful `uncheckedFromInt64` stored the magnitude and the sign of a value that is not the smallest. -/
lemma STAmount.uncheckedFromInt64_eq_ok {nt : NumericType} {v : Int64} {o : Int} {r : STAmount} :
    STAmount.uncheckedFromInt64 nt v o = .ok r ↔
      v ≠ Int64.minValue ∧ STAmount.unchecked nt v.magnitude o (decide (v < 0)) = r := by
  constructor
  · intro h
    by_cases hv : v = Int64.minValue
    · subst hv; cases h
    · rw [STAmount.uncheckedFromInt64_of_ne nt o hv] at h; cases h; exact ⟨hv, rfl⟩
  · rintro ⟨hv, rfl⟩; exact STAmount.uncheckedFromInt64_of_ne nt o hv

lemma STAmount.uncheckedFromInt64_eq_error {nt : NumericType} {v : Int64} {o : Int} {e : Error}
    (h : STAmount.uncheckedFromInt64 nt v o = .error e) : e = .wrap := by
  by_cases hv : v = Int64.minValue
  · subst hv; cases h; rfl
  · rw [STAmount.uncheckedFromInt64_of_ne nt o hv] at h; cases h

@[simp] lemma STAmount.uncheckedFromInt64_ne_notLawful (nt : NumericType) (v : Int64) (o : Int) :
    STAmount.uncheckedFromInt64 nt v o ≠ .error .notLawful :=
  fun h => nomatch STAmount.uncheckedFromInt64_eq_error h

/-- The smallest `Int64` cannot be negated, so `uncheckedFromInt64` stops with the wrap error. -/
lemma STAmount.uncheckedFromInt64_minValue (nt : NumericType) (o : Int) :
    STAmount.uncheckedFromInt64 nt Int64.minValue o = .error .wrap := rfl

/-- The sign `ofIOUAmount` stores is the sign of the mantissa. -/
lemma IOUAmount.signum_neg_decide (a : IOUAmount) : decide (a.signum < 0) = decide (a.mantissa_ < 0) := by
  unfold IOUAmount.signum
  by_cases h : a.mantissa_ < 0
  · simp [h]
  · rw [ite_eq_right h]; split <;> simp [h]

/-- `ofIOUAmount` canonicalizes the magnitude and the sign of any mantissa but the smallest `Int64`. -/
lemma STAmount.ofIOUAmount_of_ne {a : IOUAmount} (mode : rounding_mode) (h : a.mantissa_ ≠ Int64.minValue) :
    STAmount.ofIOUAmount a mode =
      (STAmount.unchecked .fractional a.mantissa_.magnitude a.exponent_ (decide (a.signum < 0))).canonicalize
        mode := by
  unfold STAmount.ofIOUAmount
  rw [STAmount.uncheckedFromInt64_of_ne _ _ h, ok_bind, IOUAmount.signum_neg_decide]

/-- A successful `ofIOUAmount` canonicalized the magnitude and the sign of a mantissa that is not the smallest. -/
lemma STAmount.ofIOUAmount_ok_peel {a : IOUAmount} {mode : rounding_mode} {r : STAmount}
    (h : STAmount.ofIOUAmount a mode = .ok r) :
    a.mantissa_ ≠ Int64.minValue ∧
      (STAmount.unchecked .fractional a.mantissa_.magnitude a.exponent_ (decide (a.signum < 0))).canonicalize
        mode = .ok r := by
  by_cases hv : a.mantissa_ = Int64.minValue
  · unfold STAmount.ofIOUAmount at h
    rw [hv, STAmount.uncheckedFromInt64_minValue, err_bind] at h; cases h
  · exact ⟨hv, by rwa [STAmount.ofIOUAmount_of_ne mode hv] at h⟩

end XRPL.Model.Protocol
