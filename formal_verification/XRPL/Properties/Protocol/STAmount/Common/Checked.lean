import XRPL.Model.Protocol.STAmount
import XRPL.Properties.Protocol.Common.FixedWidth

/-! # STAmount conversions through the checked operations

`iou` and `intAmount` read the signed value through a checked `Int64` conversion. It succeeds whenever the stored
value fits, and a successful conversion gives the value the raw conversion gave. -/

namespace XRPL.Model.Protocol

/-- The checked `Int64` view of `signedDrops` succeeds when the magnitude fits. -/
lemma STAmount.signedDrops_toInt64Checked (s : STAmount) (h : s.mValue.toNat < 2 ^ 63) :
    s.signedDrops.toInt64Checked = .ok s.signedDrops.toInt64 :=
  Int.toInt64Checked_of_bounds (by unfold STAmount.signedDrops; split <;> omega)
    (by unfold STAmount.signedDrops; split <;> omega)

/-- A successful `iou` read the signed value exactly and normalized it. -/
lemma STAmount.iou_ok_peel {s : STAmount} {mode : rounding_mode} {i : IOUAmount} (hint : ¬ s.integral = true)
    (h : s.iou mode = .ok i) : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode = .ok i := by
  unfold STAmount.iou at h
  rw [if_neg hint] at h
  obtain ⟨m, hm, h⟩ := bind_ok_peel _ _ _ h
  obtain ⟨-, rfl⟩ := Int.toInt64Checked_eq_ok.mp hm
  exact h

/-- `iou` of a fractional amount whose value fits an `Int64` normalizes its signed value. -/
lemma STAmount.iou_of_lt {s : STAmount} (mode : rounding_mode) (hint : ¬ s.integral = true)
    (h : s.mValue.toNat < 2 ^ 63) :
    s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
  unfold STAmount.iou
  rw [if_neg hint, STAmount.signedDrops_toInt64Checked s h, ok_bind]

end XRPL.Model.Protocol
