import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU

/-! # Negation of an STAmount

`operator_neg` flips the sign flag (or is the identity on zero), keeps the numericType, offset and magnitude,
and negates the exact value. Subtraction reuses the addition results via `v1 - v2 = v1 + (-v2)`. -/

namespace XRPL.Model.Protocol

lemma STAmount.operator_neg_mNumericType (s : STAmount) :
    s.operator_neg.mNumericType = s.mNumericType := by
  unfold STAmount.operator_neg; split <;> rfl

/-- Negating an amount keeps whether it is an XRP or MPT amount. -/
lemma STAmount.operator_neg_integral (s : STAmount) : s.operator_neg.integral = s.integral := by
  unfold STAmount.integral
  rw [STAmount.operator_neg_mNumericType]

lemma STAmount.operator_neg_mOffset (s : STAmount) : s.operator_neg.mOffset = s.mOffset := by
  unfold STAmount.operator_neg; split <;> rfl

lemma STAmount.operator_neg_mValue (s : STAmount) : s.operator_neg.mValue = s.mValue := by
  unfold STAmount.operator_neg; split <;> rfl

/-- A zero-magnitude STAmount has value `0`. -/
lemma STAmount.toRat_eq_zero_of_mValue_zero (s : STAmount) (h : s.mValue = 0) : s.toRat = 0 := by
  have habs := STAmount.abs_toRat s
  rw [h] at habs
  simp only [UInt64.toNat_ofNat, Nat.zero_mod, Nat.cast_zero, zero_mul] at habs
  exact abs_eq_zero.mp habs

/-- `operator_neg` negates the exact value. -/
lemma STAmount.operator_neg_toRat (s : STAmount) : s.operator_neg.toRat = -s.toRat := by
  unfold STAmount.operator_neg
  split
  case isTrue h =>
    rw [beq_iff_eq] at h
    rw [STAmount.toRat_eq_zero_of_mValue_zero s h]; ring
  case isFalse h =>
    by_cases hn : s.mIsNegative = true
    · have h1 : ({s with mIsNegative := !s.mIsNegative} : STAmount).toRat
          = (s.mValue.toNat : ℚ) * 10 ^ s.mOffset := STAmount.toRat_of_nonneg _ (by simp [hn])
      have h2 : s.toRat = -((s.mValue.toNat : ℚ) * 10 ^ s.mOffset) := STAmount.toRat_of_neg s hn
      rw [h1, h2, neg_neg]
    · have hf : s.mIsNegative = false := by simpa using hn
      have h1 : ({s with mIsNegative := !s.mIsNegative} : STAmount).toRat
          = -((s.mValue.toNat : ℚ) * 10 ^ s.mOffset) := STAmount.toRat_of_neg _ (by simp [hf])
      have h2 : s.toRat = (s.mValue.toNat : ℚ) * 10 ^ s.mOffset := STAmount.toRat_of_nonneg s hf
      rw [h1, h2]

/-- An `IntegralCanonical` amount stays `IntegralCanonical` under negation. -/
lemma STAmount.IntegralCanonical.operator_neg {s : STAmount} (h : s.IntegralCanonical) :
    s.operator_neg.IntegralCanonical where
  is_integral := by rw [STAmount.operator_neg_mNumericType]; exact h.is_integral
  offset_zero := by rw [STAmount.operator_neg_mOffset]; exact h.offset_zero
  in_range := by
    rw [STAmount.operator_neg_mNumericType, STAmount.operator_neg_mValue]; exact h.in_range

/-- An `IOUCanonical` amount stays `IOUCanonical` under negation (sign-flip only). -/
lemma STAmount.IOUCanonical.operator_neg {s : STAmount} (h : s.IOUCanonical) :
    s.operator_neg.IOUCanonical where
  is_fractional := by rw [STAmount.operator_neg_mNumericType]; exact h.is_fractional
  mant_lo := by rw [STAmount.operator_neg_mValue]; exact h.mant_lo
  mant_hi := by rw [STAmount.operator_neg_mValue]; exact h.mant_hi
  exp_lo := by rw [STAmount.operator_neg_mOffset]; exact h.exp_lo
  exp_hi := by rw [STAmount.operator_neg_mOffset]; exact h.exp_hi

/-- A nonzero IOU `STAmount` difference means the exact difference is nonzero, since `v1 - v2 = v1 + (-v2)`. -/
lemma STAmount.operator_sub_iou_truth_ne_of_result (v1 v2 result : STAmount) (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.operator_sub v1 v2 mode = .ok result) (hresult : result.mValue ≠ 0) :
    v1.toRat - v2.toRat ≠ 0 := by
  have h := STAmount.operator_add_iou_truth_ne_of_result v1 v2.operator_neg result mode hc1
    hc2.operator_neg hok hresult
  rwa [STAmount.operator_neg_toRat, ← sub_eq_add_neg] at h

end XRPL.Model.Protocol
