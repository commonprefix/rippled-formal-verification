import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
-- Re-exported for the files that import this one (these lemmas moved to Protocol)
import XRPL.Properties.Protocol.Common.AmountArith
import XRPL.Properties.Protocol.Common.Reduction

/-! # Basic facts

Generic facts about `ℚ`, `ℤ`, `Int64` and `Except` used by the vault proofs. -/

namespace XRPL.Model.Protocol

/-- The two modeled integral asset types both fit `maxRep`. -/
lemma NumericType.maxValue_le_maxRep_of_real (nt : NumericType)
    (hnt : nt = .int64 ∨ nt = .native) :
    nt.maxValue.toNat ≤ maxRep.toNat := by
  rcases hnt with h | h <;> rw [h] <;> decide

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
