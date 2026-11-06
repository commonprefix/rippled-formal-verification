import XRPL.Properties.Protocol.STAmount.Add.Common.Integral

/-! # Value of a non-negative integral (XRP/MPT) amount -/

namespace XRPL.Model.Protocol

/-- For a non-negative offset-0 STAmount, `toRat` is just its `mValue`. -/
lemma STAmount.toRat_of_nonneg_offset_zero (s : STAmount) (hn : s.mIsNegative = false)
    (ho : s.mOffset = 0) : s.toRat = (s.mValue.toNat : ℚ) := by
  rw [STAmount.toRat_of_offset_zero s ho]
  unfold STAmount.signedDrops; rw [hn]; simp

end XRPL.Model.Protocol
