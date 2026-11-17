import XRPL.Model.Protocol.STAmount
import XRPL.Properties.Protocol.Common.FixedWidth

/-! # STAmount conversions to a signed value

`intAmount` reads the signed value through a checked `Int64` conversion, which succeeds whenever the stored value fits.
`iou` casts the stored mantissa to `Int64` as C++ does, which is the `Int64` view of the signed value. -/

namespace XRPL.Model.Protocol

/-- The checked `Int64` view of `signedDrops` succeeds when the magnitude fits. -/
lemma STAmount.signedDrops_toInt64Checked (s : STAmount) (h : s.mValue.toNat < 2 ^ 63) :
    s.signedDrops.toInt64Checked = .ok s.signedDrops.toInt64 :=
  Int.toInt64Checked_of_bounds (by unfold STAmount.signedDrops; split <;> omega)
    (by unfold STAmount.signedDrops; split <;> omega)

/-- The mantissa `iou` builds (cast to `Int64`, negated for a negative amount) is the `Int64` view of `signedDrops`. -/
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

/-- `iou` of a fractional amount normalizes the `Int64` view of its signed value. -/
lemma STAmount.iou_eq {s : STAmount} (mode : rounding_mode) (hint : ¬ s.integral = true) :
    s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
  unfold STAmount.iou
  rw [if_neg hint, STAmount.signedDrops_toInt64]

/-- A successful `iou` normalized the `Int64` view of the signed value. -/
lemma STAmount.iou_ok_peel {s : STAmount} {mode : rounding_mode} {i : IOUAmount} (hint : ¬ s.integral = true)
    (h : s.iou mode = .ok i) : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode = .ok i := by
  rwa [STAmount.iou_eq mode hint] at h

end XRPL.Model.Protocol
