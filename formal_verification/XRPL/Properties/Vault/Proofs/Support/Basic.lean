import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
-- Re-exported for the files that import this one
import XRPL.Properties.Protocol.Common.AmountArith
import XRPL.Properties.Protocol.Common.Reduction

/-! # Basic facts

Generic `Int64` facts used by the vault proofs. -/

namespace XRPL.Model.Protocol

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

end XRPL.Model.Protocol
