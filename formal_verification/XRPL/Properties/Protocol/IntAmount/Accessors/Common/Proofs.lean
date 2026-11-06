import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount

/-! # Proofs of the `IntAmount` accessor theorems -/

namespace XRPL.Model.Protocol

/-- The integer cast of `value` is `toRat`. -/
theorem IntAmount.value_toRat_proof (x : IntAmount) :
    ((IntAmount.value x).toInt : ℚ) = x.toRat := rfl

end XRPL.Model.Protocol
